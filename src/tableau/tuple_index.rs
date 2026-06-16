// Port of org.semanticweb.HermiT.tableau.TupleIndex (and its nested
// TrieNodeManager and TupleIndexRetrieval).
//
// A trie that indexes tuples by a projection of their columns (the "indexing
// sequence"), mapping each distinct key sequence to a tuple index, and
// supporting retrieval of all tuples whose leading (selected) columns match
// given bindings.
//
// HermiT stores the trie nodes in paged int/Object arrays with a hand-rolled
// bucket hash for child lookup; this port keeps the same trie/retrieval logic
// over an arena of nodes with a `(parent, object) -> child` map. The Java code
// overloads one slot for both FIRST_CHILD and TUPLE_INDEX (a leaf has no
// children); here they are separate fields, which is behaviourally identical.

use std::collections::HashMap;
use std::hash::Hash;

const NONE: i32 = -1;

struct TrieNode<T> {
    parent: i32,
    first_child: i32,
    previous_sibling: i32,
    next_sibling: i32,
    object: Option<T>,
    tuple_index: i32,
    /// Child trie nodes keyed by their edge object (HermiT's per-`TrieNode`
    /// bucket hash). Keeping the map on the node lets child lookup borrow the
    /// query object instead of cloning it into a global `(parent, object)` key
    /// -- the per-trie-edge `Arc` clone/drop was ~50% of saturation time.
    children: HashMap<T, usize>,
}

impl<T> TrieNode<T> {
    fn empty() -> TrieNode<T> {
        TrieNode {
            parent: NONE,
            first_child: NONE,
            previous_sibling: NONE,
            next_sibling: NONE,
            object: None,
            tuple_index: NONE,
            children: HashMap::new(),
        }
    }
}

pub struct TupleIndex<T> {
    indexing_sequence: Vec<usize>,
    nodes: Vec<TrieNode<T>>,
    free: Vec<usize>,
    root: usize,
}

impl<T: Clone + Eq + Hash> TupleIndex<T> {
    pub fn new(indexing_sequence: Vec<usize>) -> TupleIndex<T> {
        let mut index = TupleIndex {
            indexing_sequence,
            nodes: Vec::new(),
            free: Vec::new(),
            root: 0,
        };
        index.clear();
        index
    }

    pub fn get_indexing_sequence(&self) -> &[usize] {
        &self.indexing_sequence
    }

    pub fn clear(&mut self) {
        self.nodes.clear();
        self.free.clear();
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

    fn get_child_node(&self, parent: usize, object: &T) -> i32 {
        match self.nodes[parent].children.get(object) {
            Some(&child) => child as i32,
            None => NONE,
        }
    }

    fn get_child_node_add_if_necessary(&mut self, parent: usize, object: &T) -> usize {
        if let Some(&child) = self.nodes[parent].children.get(object) {
            return child;
        }
        let child = self.new_trie_node();
        let next_sibling = self.nodes[parent].first_child;
        if next_sibling != NONE {
            self.nodes[next_sibling as usize].previous_sibling = child as i32;
        }
        self.nodes[parent].first_child = child as i32;
        self.nodes[child].parent = parent as i32;
        self.nodes[child].first_child = NONE;
        self.nodes[child].previous_sibling = NONE;
        self.nodes[child].next_sibling = next_sibling;
        self.nodes[child].object = Some(object.clone());
        self.nodes[child].tuple_index = NONE;
        self.nodes[parent].children.insert(object.clone(), child);
        child
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
        let object = self.nodes[trie_node].object.clone();
        let parent = self.nodes[trie_node].parent;
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
        if let (Some(object), true) = (object, parent != NONE) {
            self.nodes[parent as usize].children.remove(&object);
        }
        self.free.push(trie_node);
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
    selection_indices: Vec<usize>,
    indexing_sequence_length: usize,
    current_trie_node: i32,
}

impl<'a, T: Clone + Eq + Hash> TupleIndexRetrieval<'a, T> {
    pub fn new(
        tuple_index: &'a TupleIndex<T>,
        bindings_buffer: &'a [Option<T>],
        selection_indices: Vec<usize>,
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
