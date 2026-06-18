// Port of org.semanticweb.HermiT.tableau.TupleIndex (and its nested
// TrieNodeManager and TupleIndexRetrieval).
//
// A trie that indexes tuples by a projection of their columns (the "indexing
// sequence"), mapping each distinct key sequence to a tuple index, and
// supporting retrieval of all tuples whose leading (selected) columns match
// given bindings.
//
// HermiT stores the trie nodes in paged int/Object arrays and resolves a child
// `(parent, object) -> child` through ONE global open-addressed bucket array
// (`m_buckets`: an `int[]` holding trie-node ids, hashed on `object.hashCode() +
// parent`), with the collision chain threaded through the trie nodes themselves
// (`TRIE_NODE_NEXT_ENTRY`). This port mirrors that exactly: a flat `buckets`
// vector plus a `next_entry` link per node, rather than a separate `HashMap` per
// trie node. (An earlier revision used a per-node map to avoid cloning the edge
// object into a `(parent, object)` key when objects were `Arc`-interned and a
// clone was costly; objects are now `Copy` handles, so the global bucket array --
// Java's design -- is both faithful and cheaper: no per-node hash-table
// allocation and one cache-friendly array.) The Java code overloads one slot for
// both FIRST_CHILD and TUPLE_INDEX (a leaf has no children); here they are
// separate fields, which is behaviourally identical.

use std::hash::{Hash, Hasher};

const NONE: i32 = -1;
const INITIAL_BUCKETS: usize = 16;
const LOAD_FACTOR: f64 = 0.7;

// The trie nodes are stored struct-of-arrays (Java's layout): the `i32` link
// fields live in `TrieNode` (in `nodes`), while the edge `object` lives in a
// parallel `objects` vector indexed by the same node id. The hot chain walks
// (bucket collision chains) and sibling walks (retrieval) read only the link
// fields, so keeping the 24-byte `Option<TableauObject>` out of `TrieNode`
// triples the node density per cache line and avoids pulling the object into
// cache when only links are needed.
struct TrieNode {
    parent: i32,
    first_child: i32,
    previous_sibling: i32,
    next_sibling: i32,
    tuple_index: i32,
    /// Next trie node in the same bucket's collision chain (Java's
    /// `TRIE_NODE_NEXT_ENTRY`); `NONE` at the end of the chain.
    next_entry: i32,
}

impl TrieNode {
    fn empty() -> TrieNode {
        TrieNode {
            parent: NONE,
            first_child: NONE,
            previous_sibling: NONE,
            next_sibling: NONE,
            tuple_index: NONE,
            next_entry: NONE,
        }
    }
}

pub struct TupleIndex<T> {
    indexing_sequence: Vec<usize>,
    nodes: Vec<TrieNode>,
    /// The edge object of each node (`None` for the root), parallel to `nodes`
    /// (struct-of-arrays, mirroring Java's separate object array).
    objects: Vec<Option<T>>,
    free: Vec<usize>,
    root: usize,
    /// Open-addressed bucket array (`m_buckets`): each entry is a trie-node id or
    /// `NONE`. Length is a power of two; `buckets_mask == len - 1`.
    buckets: Vec<i32>,
    buckets_mask: usize,
    resize_threshold: usize,
    /// Number of non-root trie nodes held in `buckets` (Java `m_numberOfNodes`).
    number_of_nodes: usize,
}

impl<T: Clone + Eq + Hash> TupleIndex<T> {
    pub fn new(indexing_sequence: Vec<usize>) -> TupleIndex<T> {
        let mut index = TupleIndex {
            indexing_sequence,
            nodes: Vec::new(),
            objects: Vec::new(),
            free: Vec::new(),
            root: 0,
            buckets: Vec::new(),
            buckets_mask: 0,
            resize_threshold: 0,
            number_of_nodes: 0,
        };
        index.clear();
        index
    }

    pub fn get_indexing_sequence(&self) -> &[usize] {
        &self.indexing_sequence
    }

    pub fn clear(&mut self) {
        self.nodes.clear();
        self.objects.clear();
        self.free.clear();
        self.buckets = vec![NONE; INITIAL_BUCKETS];
        self.buckets_mask = INITIAL_BUCKETS - 1;
        self.resize_threshold = (INITIAL_BUCKETS as f64 * LOAD_FACTOR) as usize;
        self.number_of_nodes = 0;
        // The root is created directly (it has no parent/object and is not held in
        // a bucket), so it does not count towards `number_of_nodes`.
        self.root = self.new_trie_node();
    }

    fn new_trie_node(&mut self) -> usize {
        if let Some(reused) = self.free.pop() {
            self.nodes[reused] = TrieNode::empty();
            self.objects[reused] = None;
            reused
        } else {
            self.nodes.push(TrieNode::empty());
            self.objects.push(None);
            self.nodes.len() - 1
        }
    }

    /// Bucket for the edge `(parent, object)` (Java `getIndexFor(object.hashCode()
    /// + parent, mask)`). Bucket distribution only affects lookup cost, never the
    /// trie's content or sibling (retrieval) order, so any good mix works.
    /// Mixed hash of the edge `(parent, object)`, unmasked. Java:
    /// `getIndexFor(object.hashCode() + parent, mask)` -- hash the object once and
    /// add `parent` as an integer (cheap), then run Java's `getIndexFor` avalanche
    /// (widened) so the low bits are well distributed. `bucket_index` and
    /// `resize_buckets` MUST use this same value (only the mask differs), or a
    /// resize would move nodes to buckets a later lookup can't find.
    #[inline]
    fn edge_hash(object: &T, parent: usize) -> usize {
        let mut hasher = rustc_hash::FxHasher::default();
        object.hash(&mut hasher);
        let mut h = (hasher.finish() as usize).wrapping_add(parent);
        h = h.wrapping_add(!(h << 9));
        h ^= h >> 14;
        h = h.wrapping_add(h << 4);
        h ^= h >> 10;
        h
    }

    #[inline]
    fn bucket_index(&self, object: &T, parent: usize) -> usize {
        Self::edge_hash(object, parent) & self.buckets_mask
    }

    fn get_child_node(&self, parent: usize, object: &T) -> i32 {
        let bucket = self.bucket_index(object, parent);
        let mut child = self.buckets[bucket];
        while child != NONE {
            let node = &self.nodes[child as usize];
            if node.parent == parent as i32
                && self.objects[child as usize].as_ref() == Some(object)
            {
                return child;
            }
            child = node.next_entry;
        }
        NONE
    }

    fn get_child_node_add_if_necessary(&mut self, parent: usize, object: &T) -> usize {
        // Look up the existing child along the bucket's collision chain.
        let mut bucket = self.bucket_index(object, parent);
        let mut child = self.buckets[bucket];
        while child != NONE {
            let node = &self.nodes[child as usize];
            if node.parent == parent as i32
                && self.objects[child as usize].as_ref() == Some(object)
            {
                return child as usize;
            }
            child = node.next_entry;
        }
        // Not present: grow the bucket array if past the load factor, then create
        // the node and link it into the parent's sibling list and the bucket chain.
        if self.number_of_nodes >= self.resize_threshold {
            self.resize_buckets();
            bucket = self.bucket_index(object, parent);
        }
        let child = self.new_trie_node();
        let next_sibling = self.nodes[parent].first_child;
        if next_sibling != NONE {
            self.nodes[next_sibling as usize].previous_sibling = child as i32;
        }
        self.nodes[parent].first_child = child as i32;
        let bucket_head = self.buckets[bucket];
        let node = &mut self.nodes[child];
        node.parent = parent as i32;
        node.first_child = NONE;
        node.previous_sibling = NONE;
        node.next_sibling = next_sibling;
        node.tuple_index = NONE;
        node.next_entry = bucket_head;
        self.objects[child] = Some(object.clone());
        self.buckets[bucket] = child as i32;
        self.number_of_nodes += 1;
        child
    }

    fn resize_buckets(&mut self) {
        let new_len = self.buckets.len() * 2;
        let new_mask = new_len - 1;
        let mut new_buckets = vec![NONE; new_len];
        for bucket in 0..self.buckets.len() {
            let mut node = self.buckets[bucket];
            while node != NONE {
                let next = self.nodes[node as usize].next_entry;
                let parent = self.nodes[node as usize].parent as usize;
                let new_bucket = {
                    let object = self.objects[node as usize]
                        .as_ref()
                        .expect("a bucketed trie node has an object");
                    Self::edge_hash(object, parent) & new_mask
                };
                self.nodes[node as usize].next_entry = new_buckets[new_bucket];
                new_buckets[new_bucket] = node;
                node = next;
            }
        }
        self.buckets = new_buckets;
        self.buckets_mask = new_mask;
        self.resize_threshold = (new_len as f64 * LOAD_FACTOR) as usize;
    }

    pub fn add_tuple(&mut self, tuple: &[T], potential_tuple_index: i32) -> i32 {
        let mut trie_node = self.root;
        for seq_index in 0..self.indexing_sequence.len() {
            let column = self.indexing_sequence[seq_index];
            let object = tuple[column].clone();
            trie_node = self.get_child_node_add_if_necessary(trie_node, &object);
        }
        if self.nodes[trie_node].tuple_index == NONE {
            self.nodes[trie_node].tuple_index = potential_tuple_index;
            potential_tuple_index
        } else {
            self.nodes[trie_node].tuple_index
        }
    }

    pub fn get_tuple_index(&self, tuple: &[T]) -> i32 {
        let mut trie_node = self.root as i32;
        for &column in &self.indexing_sequence {
            trie_node = self.get_child_node(trie_node as usize, &tuple[column]);
            if trie_node == NONE {
                return NONE;
            }
        }
        self.nodes[trie_node as usize].tuple_index
    }

    pub fn remove_tuple(&mut self, tuple: &[T]) -> i32 {
        let mut leaf = self.root as i32;
        for &column in &self.indexing_sequence {
            leaf = self.get_child_node(leaf as usize, &tuple[column]);
            if leaf == NONE {
                return NONE;
            }
        }
        let leaf = leaf as usize;
        let tuple_index = self.nodes[leaf].tuple_index;
        let mut trie_node = self.nodes[leaf].parent;
        self.remove_trie_node(leaf);
        while trie_node != self.root as i32 && self.nodes[trie_node as usize].first_child == NONE {
            let parent = self.nodes[trie_node as usize].parent;
            self.remove_trie_node(trie_node as usize);
            trie_node = parent;
        }
        tuple_index
    }

    fn remove_trie_node(&mut self, trie_node: usize) {
        // Only non-root nodes are removed (the trie is pruned up to, not
        // including, the root), so the node is always present in its bucket chain.
        let parent = self.nodes[trie_node].parent;
        let bucket = {
            let object = self.objects[trie_node]
                .as_ref()
                .expect("a removable trie node has an object");
            self.bucket_index(object, parent as usize)
        };
        let mut child = self.buckets[bucket];
        let mut previous_child = NONE;
        while child != NONE {
            let next = self.nodes[child as usize].next_entry;
            if child as usize == trie_node {
                self.number_of_nodes -= 1;
                // Unlink from the parent's sibling list.
                let previous_sibling = self.nodes[trie_node].previous_sibling;
                let next_sibling = self.nodes[trie_node].next_sibling;
                if previous_sibling == NONE {
                    if parent != NONE {
                        self.nodes[parent as usize].first_child = next_sibling;
                    }
                } else {
                    self.nodes[previous_sibling as usize].next_sibling = next_sibling;
                }
                if next_sibling != NONE {
                    self.nodes[next_sibling as usize].previous_sibling = previous_sibling;
                }
                // Unlink from the bucket's collision chain.
                if previous_child == NONE {
                    self.buckets[bucket] = next;
                } else {
                    self.nodes[previous_child as usize].next_entry = next;
                }
                self.free.push(trie_node);
                return;
            }
            previous_child = child;
            child = next;
        }
        unreachable!("trie node to remove was not found in its bucket chain");
    }

    // Accessors used by the retrieval cursor.
    fn first_child(&self, node: i32) -> i32 {
        self.nodes[node as usize].first_child
    }
    fn next_sibling(&self, node: i32) -> i32 {
        self.nodes[node as usize].next_sibling
    }
    fn parent(&self, node: i32) -> i32 {
        self.nodes[node as usize].parent
    }
    fn tuple_index_at(&self, node: i32) -> i32 {
        self.nodes[node as usize].tuple_index
    }
}

/// A cursor over all tuples whose selected columns match the given bindings
/// (the Java `TupleIndex.TupleIndexRetrieval`).
pub struct TupleIndexRetrieval<'a, T: Clone + Eq + Hash> {
    tuple_index: &'a TupleIndex<T>,
    bindings_buffer: &'a [Option<T>],
    /// The bound-prefix buffer indices, borrowed from the caller's stack (the
    /// prefix is at most the arity, so the caller keeps it in a small fixed array
    /// rather than allocating a `Vec` per retrieval).
    selection_indices: &'a [usize],
    indexing_sequence_length: usize,
    current_trie_node: i32,
}

impl<'a, T: Clone + Eq + Hash> TupleIndexRetrieval<'a, T> {
    pub fn new(
        tuple_index: &'a TupleIndex<T>,
        bindings_buffer: &'a [Option<T>],
        selection_indices: &'a [usize],
    ) -> TupleIndexRetrieval<'a, T> {
        let indexing_sequence_length = tuple_index.indexing_sequence.len();
        TupleIndexRetrieval {
            tuple_index,
            bindings_buffer,
            selection_indices,
            indexing_sequence_length,
            current_trie_node: NONE,
        }
    }

    pub fn open(&mut self) {
        let selection_len = self.selection_indices.len();
        self.current_trie_node = self.tuple_index.root as i32;
        for position in 0..selection_len {
            // The selected columns are always bound (`Some`) -- the retrieval is
            // only built over a bound prefix -- so read the slot directly.
            let object = self.bindings_buffer[self.selection_indices[position]]
                .as_ref()
                .expect("selected binding slot is set");
            self.current_trie_node = self
                .tuple_index
                .get_child_node(self.current_trie_node as usize, object);
            if self.current_trie_node == NONE {
                return;
            }
        }
        if selection_len == 0 && self.tuple_index.first_child(self.tuple_index.root as i32) == NONE {
            self.current_trie_node = NONE;
        } else {
            for _ in selection_len..self.indexing_sequence_length {
                self.current_trie_node = self.tuple_index.first_child(self.current_trie_node);
            }
        }
    }

    pub fn after_last(&self) -> bool {
        self.current_trie_node == NONE
    }

    pub fn get_current_tuple_index(&self) -> i32 {
        self.tuple_index.tuple_index_at(self.current_trie_node)
    }

    pub fn next(&mut self) {
        let selection_len = self.selection_indices.len();
        let mut trie_node_depth = self.indexing_sequence_length;
        while trie_node_depth != selection_len
            && self.tuple_index.next_sibling(self.current_trie_node) == NONE
        {
            self.current_trie_node = self.tuple_index.parent(self.current_trie_node);
            trie_node_depth -= 1;
        }
        if trie_node_depth == selection_len {
            self.current_trie_node = NONE;
        } else {
            self.current_trie_node = self.tuple_index.next_sibling(self.current_trie_node);
            for _ in trie_node_depth..self.indexing_sequence_length {
                self.current_trie_node = self.tuple_index.first_child(self.current_trie_node);
            }
        }
    }
}
