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

use std::hash::Hash;

const NONE: i32 = -1;
// Start large enough to skip the early resize storm: a dense reasoning workload
// builds millions of tuples over tens of thousands of nodes, so a 16-slot array
// (Java's default) resizes ~17 times, rehashing everything each time. 1024 slots
// (4 KiB of `i32`) is negligible and clears most of that; `clear` (below) also
// keeps a grown array's capacity across the many per-test resets, so a hot index
// only pays the resize ladder once for the whole classification.
const INITIAL_BUCKETS: usize = 1024;
const LOAD_FACTOR: f64 = 0.8;

/// A *collision-free* integer key for a tuple-index edge object: distinct
/// objects MUST map to distinct keys (not merely a good hash). This exactness is
/// what lets the trie match an edge on `(parent, key)` ALONE -- without storing
/// the object to confirm the match -- so the index needs no parallel object
/// array and the hot lookup touches one fewer cache line.
pub trait EdgeKey {
    fn unique_key(&self) -> u64;
}

impl EdgeKey for crate::tableau::object::TableauObject {
    #[inline]
    fn unique_key(&self) -> u64 {
        crate::tableau::object::TableauObject::unique_key(self)
    }
}

// Plain integer edge objects are their own collision-free key (the `i32 -> u32`
// reinterpret is a bijection, so distinct values never collide). Used by the
// tuple-index unit tests, which index over raw `i32` edge objects.
impl EdgeKey for i32 {
    #[inline]
    fn unique_key(&self) -> u64 {
        *self as u32 as u64
    }
}

// The trie nodes hold only `i32` link fields plus the edge's collision-free
// `key`. Because `key` exactly identifies the edge object (see `EdgeKey`), the
// chain walk's `(parent, key)` compare IS the match -- there is no separate
// `objects` array to consult and no object clone to store, which both shrinks the
// index (less DRAM traffic on this bandwidth-bound hot path) and removes a cache
// miss per successful lookup.
struct TrieNode {
    parent: i32,
    first_child: i32,
    previous_sibling: i32,
    next_sibling: i32,
    tuple_index: i32,
    /// Next trie node in the same bucket's collision chain (Java's
    /// `TRIE_NODE_NEXT_ENTRY`); `NONE` at the end of the chain.
    next_entry: i32,
    /// The edge object's collision-free `unique_key`. The chain walk filters on
    /// `(parent, key)`, which is exact (distinct objects never share a key), so a
    /// match here is the match -- no object dereference needed.
    key: u64,
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
            key: 0,
        }
    }
}

pub struct TupleIndex<T> {
    indexing_sequence: Vec<usize>,
    nodes: Vec<TrieNode>,
    free: Vec<usize>,
    root: usize,
    /// Open-addressed bucket array (`m_buckets`): each entry is a trie-node id or
    /// `NONE`. Length is a power of two; `buckets_mask == len - 1`.
    buckets: Vec<i32>,
    buckets_mask: usize,
    resize_threshold: usize,
    /// Number of non-root trie nodes held in `buckets` (Java `m_numberOfNodes`).
    number_of_nodes: usize,
    _marker: std::marker::PhantomData<T>,
}

impl<T: Clone + Eq + Hash + EdgeKey> TupleIndex<T> {
    pub fn new(indexing_sequence: Vec<usize>) -> TupleIndex<T> {
        let mut index = TupleIndex {
            indexing_sequence,
            nodes: Vec::new(),
            free: Vec::new(),
            root: 0,
            buckets: Vec::new(),
            buckets_mask: 0,
            resize_threshold: 0,
            number_of_nodes: 0,
            _marker: std::marker::PhantomData,
        };
        index.clear();
        index
    }

    pub fn get_indexing_sequence(&self) -> &[usize] {
        &self.indexing_sequence
    }

    /// Retained trie-node + bucket capacity in elements (oversize detection).
    pub(crate) fn retained_capacity(&self) -> usize {
        self.nodes.capacity() + self.buckets.capacity()
    }

    pub fn clear(&mut self) {
        self.nodes.clear();
        self.free.clear();
        // `clear` runs once per satisfiability test during classification (many
        // times). Reuse the existing bucket allocation -- refill with `NONE`
        // rather than reallocate -- so a hot loop of tests doesn't thrash the
        // allocator. Keep a grown array's capacity (a test that needed more
        // buckets last time likely needs them again); only ensure it is at least
        // `INITIAL_BUCKETS` and a power of two.
        let len = self.buckets.len().max(INITIAL_BUCKETS);
        debug_assert!(len.is_power_of_two());
        if self.buckets.len() == len {
            self.buckets.iter_mut().for_each(|b| *b = NONE);
        } else {
            self.buckets.clear();
            self.buckets.resize(len, NONE);
        }
        self.buckets_mask = len - 1;
        self.resize_threshold = (len as f64 * LOAD_FACTOR) as usize;
        self.number_of_nodes = 0;
        // The root is created directly (it has no parent/object and is not held in
        // a bucket), so it does not count towards `number_of_nodes`.
        self.root = self.new_trie_node();
    }

    fn new_trie_node(&mut self) -> usize {
        if let Some(reused) = self.free.pop() {
            self.nodes[reused] = TrieNode::empty();
            reused
        } else {
            self.nodes.push(TrieNode::empty());
            self.nodes.len() - 1
        }
    }

    /// Avalanche of the edge `(key, parent)` (`key` is the object's collision-free
    /// `unique_key`), unmasked. Java caches `object.hashCode()` and does
    /// `getIndexFor(hashCode + parent, mask)`; here `key` is an already-mixed word
    /// (interned id with variant tag), added to `parent` and run through the same
    /// `getIndexFor` avalanche so the low bits are well distributed. Every caller
    /// (lookup, insert, `resize_buckets`, `remove_trie_node`) MUST use this same
    /// value (only the mask differs), or a resize would move nodes to buckets a
    /// later lookup can't find. Bucket distribution only affects lookup cost,
    /// never the trie's content or sibling (retrieval) order, so any good mix works.
    #[inline]
    fn edge_hash_key(key: u64, parent: usize) -> usize {
        let mut h = (key as usize).wrapping_add(parent);
        h = h.wrapping_add(!(h << 9));
        h ^= h >> 14;
        h = h.wrapping_add(h << 4);
        h ^= h >> 10;
        h
    }

    #[inline]
    fn get_child_node(&self, parent: usize, object: &T) -> i32 {
        let key = object.unique_key();
        let bucket = Self::edge_hash_key(key, parent) & self.buckets_mask;
        let mut child = self.buckets[bucket];
        let parent = parent as i32;
        while child != NONE {
            // `(parent, key)` is an EXACT match -- `key` is collision-free, so two
            // distinct edge objects never share it -- hence no object dereference
            // is needed to confirm; the chain walk touches only the `nodes` array.
            //
            // `child` is always a live node id (it came from a bucket head or a
            // `next_entry` link, both of which only ever hold ids `< nodes.len()`),
            // so the per-step bounds check is provably redundant; eliding it keeps
            // the collision-chain walk to a single `nodes` load per step.
            let c = child as usize;
            let node = unsafe { self.nodes.get_unchecked(c) };
            if node.parent == parent && node.key == key {
                return child;
            }
            child = node.next_entry;
        }
        NONE
    }

    fn get_child_node_add_if_necessary(&mut self, parent: usize, object: &T) -> usize {
        let key = object.unique_key();
        // Look up the existing child along the bucket's collision chain.
        let mut bucket = Self::edge_hash_key(key, parent) & self.buckets_mask;
        let mut child = self.buckets[bucket];
        let parent_i = parent as i32;
        while child != NONE {
            // Same invariant as `get_child_node`: `child` is always a live node id
            // (`< nodes.len()`), having come from a bucket head or a `next_entry`
            // link, so the per-step bounds check is provably redundant -- eliding it
            // keeps the insert-path collision-chain walk to one `nodes` load per step.
            let node = unsafe { self.nodes.get_unchecked(child as usize) };
            if node.parent == parent_i && node.key == key {
                return child as usize;
            }
            child = node.next_entry;
        }
        // Not present: grow the bucket array if past the load factor, then create
        // the node and link it into the parent's sibling list and the bucket chain.
        if self.number_of_nodes >= self.resize_threshold {
            self.resize_buckets();
            bucket = Self::edge_hash_key(key, parent) & self.buckets_mask;
        }
        let child = self.new_trie_node();
        // `parent` is a live node id (the descent only passes live ids or the root),
        // `next_sibling` is NONE-checked before use, and `child` was just allocated,
        // so every node access in this insert path is provably in bounds; eliding the
        // checks keeps the hot per-test trie rebuild's inserts to bare loads/stores.
        let next_sibling = unsafe { self.nodes.get_unchecked(parent) }.first_child;
        if next_sibling != NONE {
            unsafe { self.nodes.get_unchecked_mut(next_sibling as usize) }.previous_sibling =
                child as i32;
        }
        unsafe { self.nodes.get_unchecked_mut(parent) }.first_child = child as i32;
        let bucket_head = self.buckets[bucket];
        let node = unsafe { self.nodes.get_unchecked_mut(child) };
        node.parent = parent as i32;
        node.first_child = NONE;
        node.previous_sibling = NONE;
        node.next_sibling = next_sibling;
        node.tuple_index = NONE;
        node.next_entry = bucket_head;
        node.key = key;
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
                let trie = &self.nodes[node as usize];
                let next = trie.next_entry;
                // Rehash from the inline cached key + parent (the same value
                // `edge_hash_key` uses on lookup), so no `objects` deref is needed.
                let new_bucket = Self::edge_hash_key(trie.key, trie.parent as usize) & new_mask;
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
            // `column` is a valid column of this table's `tuple` (`< arity ==
            // tuple.len()`), so the read is provably in bounds.
            let object = unsafe { tuple.get_unchecked(column) };
            trie_node = self.get_child_node_add_if_necessary(trie_node, object);
        }
        // `trie_node` is a live node id (`< nodes.len()`) returned by the descent.
        let leaf = unsafe { self.nodes.get_unchecked_mut(trie_node) };
        if leaf.tuple_index == NONE {
            leaf.tuple_index = potential_tuple_index;
            potential_tuple_index
        } else {
            leaf.tuple_index
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
        let bucket =
            Self::edge_hash_key(self.nodes[trie_node].key, parent as usize) & self.buckets_mask;
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

    // Accessors used by the retrieval cursor. These run in the tight trie-walk
    // loop of `TupleIndexRetrieval::open`/`next`; `#[inline]` lets them fold into
    // the cursor rather than incurring a call per sibling/child step.
    #[inline]
    fn first_child(&self, node: i32) -> i32 {
        self.nodes[node as usize].first_child
    }
    #[inline]
    fn next_sibling(&self, node: i32) -> i32 {
        self.nodes[node as usize].next_sibling
    }
    #[inline]
    fn parent(&self, node: i32) -> i32 {
        self.nodes[node as usize].parent
    }
    #[inline]
    fn tuple_index_at(&self, node: i32) -> i32 {
        self.nodes[node as usize].tuple_index
    }
}

/// A cursor over all tuples whose selected columns match the given bindings
/// (the Java `TupleIndex.TupleIndexRetrieval`).
pub struct TupleIndexRetrieval<'a, T: Clone + Eq + Hash + EdgeKey> {
    tuple_index: &'a TupleIndex<T>,
    bindings_buffer: &'a [Option<T>],
    /// The bound-prefix buffer indices, borrowed from the caller's stack (the
    /// prefix is at most the arity, so the caller keeps it in a small fixed array
    /// rather than allocating a `Vec` per retrieval).
    selection_indices: &'a [usize],
    indexing_sequence_length: usize,
    current_trie_node: i32,
}

impl<'a, T: Clone + Eq + Hash + EdgeKey> TupleIndexRetrieval<'a, T> {
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
