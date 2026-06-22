// Port of org.semanticweb.HermiT.graph.Graph<T>.
//
// A simple directed graph with successor sets, transitive closure, inversion
// and reachability queries, used throughout HermiT (e.g. for role and concept
// hierarchies).
//
// Memory: the successor sets can be O(n^2) in dense classification graphs
// (EFO's `possible_subsumptions`). Rather than storing the wide `T` (a
// `Class<Arc<str>>` is a 16-byte fat pointer) in every successor set, each
// distinct element is interned to a dense `u32` id once, and the successor
// sets hold those 4-byte ids. This matches Java HermiT's reference-sized set
// entries (an `AtomicConcept` object reference) and keeps dense graphs within
// RAM. Element identity/order semantics are unchanged: an element always maps
// to the same id within one graph, so a node and the same element appearing as
// a successor share an id.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::Hash;

#[derive(Debug)]
pub struct Graph<T: Eq + Hash + Clone> {
    elements: HashSet<T>,
    /// Interner: element -> dense id (every from/to ever added). `elems` is the
    /// reverse (id -> element). Ids are never reused, so they stay stable for the
    /// life of the graph.
    ids: HashMap<T, u32>,
    elems: Vec<T>,
    /// Successor sets keyed by node id, holding successor ids.
    successors_by_id: HashMap<u32, HashSet<u32>>,
}

// Hand-written Clone mirrors Graph.java:86-95: rebuild via add_edge so that
// keys whose successor sets are empty are never copied into the clone's map.
impl<T: Eq + Hash + Clone> Clone for Graph<T> {
    fn clone(&self) -> Self {
        let mut result = Graph::new();
        result.elements.extend(self.elements.iter().cloned());
        for (&from_id, successors) in &self.successors_by_id {
            let from = self.elems[from_id as usize].clone();
            for &to_id in successors {
                result.add_edge(from.clone(), self.elems[to_id as usize].clone());
            }
        }
        result
    }
}

impl<T: Eq + Hash + Clone> Default for Graph<T> {
    fn default() -> Self {
        Graph::new()
    }
}

impl<T: Eq + Hash + Clone> Graph<T> {
    pub fn new() -> Self {
        Graph {
            elements: HashSet::new(),
            ids: HashMap::new(),
            elems: Vec::new(),
            successors_by_id: HashMap::new(),
        }
    }

    /// Intern `t`, returning its (possibly new) id.
    #[inline]
    fn intern(&mut self, t: &T) -> u32 {
        if let Some(&id) = self.ids.get(t) {
            return id;
        }
        let id = self.elems.len() as u32;
        self.elems.push(t.clone());
        self.ids.insert(t.clone(), id);
        id
    }

    /// The id of `t` if it has ever been interned, else `None` (read-only).
    #[inline]
    fn id_of(&self, t: &T) -> Option<u32> {
        self.ids.get(t).copied()
    }

    pub fn add_edge(&mut self, from: T, to: T) {
        let from_id = self.intern(&from);
        let to_id = self.intern(&to);
        self.successors_by_id.entry(from_id).or_default().insert(to_id);
        self.elements.insert(from);
        self.elements.insert(to);
    }

    pub fn add_edges(&mut self, from: T, to: &HashSet<T>) {
        let from_id = self.intern(&from);
        let to_ids: Vec<u32> = to.iter().map(|t| self.intern(t)).collect();
        let successors = self.successors_by_id.entry(from_id).or_default();
        for id in to_ids {
            successors.insert(id);
        }
        self.elements.insert(from);
        for t in to {
            self.elements.insert(t.clone());
        }
    }

    pub fn get_elements(&self) -> &HashSet<T> {
        &self.elements
    }

    /// Whether `node` has no outgoing edges (mirrors
    /// `Graph.getSuccessors(node).isEmpty()`).
    pub fn successors_is_empty(&self, node: &T) -> bool {
        match self.id_of(node) {
            Some(id) => self.successors_by_id.get(&id).is_none_or(|s| s.is_empty()),
            None => true,
        }
    }

    /// Whether `node -> target` is an edge (mirrors
    /// `Graph.getSuccessors(node).contains(target)`).
    pub fn successor_contains(&self, node: &T, target: &T) -> bool {
        match (self.id_of(node), self.id_of(target)) {
            (Some(nid), Some(tid)) => {
                self.successors_by_id.get(&nid).is_some_and(|s| s.contains(&tid))
            }
            _ => false,
        }
    }

    /// Number of outgoing edges of `node`.
    pub fn successors_len(&self, node: &T) -> usize {
        match self.id_of(node) {
            Some(id) => self.successors_by_id.get(&id).map_or(0, |s| s.len()),
            None => 0,
        }
    }

    /// An owned copy of `node`'s successor set (materialised from the interned
    /// ids). Mirrors Java callers that consume an owned set.
    pub fn get_successors(&self, node: &T) -> HashSet<T> {
        match self.id_of(node) {
            Some(id) => match self.successors_by_id.get(&id) {
                Some(set) => set.iter().map(|&sid| self.elems[sid as usize].clone()).collect(),
                None => HashSet::new(),
            },
            None => HashSet::new(),
        }
    }

    pub fn transitively_close(&mut self) {
        let keys: Vec<u32> = self.successors_by_id.keys().copied().collect();
        for key in keys {
            let mut reachable: HashSet<u32> = self.successors_by_id[&key].clone();
            let mut to_process: Vec<u32> = reachable.iter().copied().collect();
            while let Some(on_path) = to_process.pop() {
                if let Some(successors) = self.successors_by_id.get(&on_path) {
                    for succ in successors.clone() {
                        if reachable.insert(succ) {
                            to_process.push(succ);
                        }
                    }
                }
            }
            self.successors_by_id.insert(key, reachable);
        }
    }

    pub fn get_inverse(&self) -> Graph<T> {
        let mut result = Graph::new();
        for (&from_id, successors) in &self.successors_by_id {
            let from = &self.elems[from_id as usize];
            for &to_id in successors {
                result.add_edge(self.elems[to_id as usize].clone(), from.clone());
            }
        }
        result
    }

    pub fn remove_elements(&mut self, elements: &HashSet<T>) {
        for element in elements {
            self.elements.remove(element);
            if let Some(id) = self.id_of(element) {
                self.successors_by_id.remove(&id);
            }
        }
    }

    pub fn is_reachable_successor(&self, from_node: &T, to_node: &T) -> bool {
        if from_node == to_node {
            return true;
        }
        let (from_id, to_id) = match (self.id_of(from_node), self.id_of(to_node)) {
            (Some(f), Some(t)) => (f, t),
            _ => return false,
        };
        let mut result: HashSet<u32> = HashSet::new();
        let mut to_visit: VecDeque<u32> = VecDeque::new();
        to_visit.push_back(from_id);
        while let Some(current) = to_visit.pop_front() {
            if let Some(successors) = self.successors_by_id.get(&current) {
                if successors.contains(&to_id) {
                    return true;
                }
                if result.insert(current) {
                    for &succ in successors {
                        to_visit.push_back(succ);
                    }
                }
            } else {
                result.insert(current);
            }
        }
        false
    }

    /// Remove `to_remove` from `node`'s successor set (no-op for absent edges).
    pub fn remove_successors(&mut self, node: &T, to_remove: &HashSet<T>) {
        let nid = match self.id_of(node) {
            Some(id) => id,
            None => return,
        };
        if let Some(successors) = self.successors_by_id.get_mut(&nid) {
            for r in to_remove {
                if let Some(&rid) = self.ids.get(r) {
                    successors.remove(&rid);
                }
            }
        }
    }

    /// Remove a single edge `node -> successor`.
    pub fn remove_edge(&mut self, node: &T, successor: &T) {
        if let (Some(nid), Some(sid)) = (self.id_of(node), self.id_of(successor)) {
            if let Some(successors) = self.successors_by_id.get_mut(&nid) {
                successors.remove(&sid);
            }
        }
    }

    /// Clear all of `node`'s outgoing edges.
    pub fn clear_successors(&mut self, node: &T) {
        if let Some(nid) = self.id_of(node) {
            if let Some(successors) = self.successors_by_id.get_mut(&nid) {
                successors.clear();
            }
        }
    }

    pub fn get_reachable_successors(&self, from_node: &T) -> HashSet<T> {
        let from_id = match self.id_of(from_node) {
            Some(id) => id,
            // Never interned: it has no edges, but the original BFS still yields
            // the start node itself (it inserts `current` before expanding).
            None => {
                let mut result = HashSet::new();
                result.insert(from_node.clone());
                return result;
            }
        };
        let mut visited: HashSet<u32> = HashSet::new();
        let mut to_visit: VecDeque<u32> = VecDeque::new();
        to_visit.push_back(from_id);
        while let Some(current) = to_visit.pop_front() {
            if visited.insert(current) {
                if let Some(successors) = self.successors_by_id.get(&current) {
                    for &succ in successors {
                        to_visit.push_back(succ);
                    }
                }
            }
        }
        visited.into_iter().map(|id| self.elems[id as usize].clone()).collect()
    }
}

// Mirrors Graph.toString(): one line per element, `element -> { s1, s2, ... }`.
// Java uses the platform line separator; we use `\n` to avoid platform-
// dependent output.
impl<T: Eq + Hash + Clone + fmt::Display> fmt::Display for Graph<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for element in &self.elements {
            write!(f, "{element} -> {{ ")?;
            let mut first_successor = true;
            if let Some(id) = self.id_of(element) {
                if let Some(successors) = self.successors_by_id.get(&id) {
                    for &sid in successors {
                        if first_successor {
                            first_successor = false;
                        } else {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", self.elems[sid as usize])?;
                    }
                }
            }
            writeln!(f, " }}")?;
        }
        Ok(())
    }
}
