// Port of org.semanticweb.HermiT.graph.Graph<T>.
//
// A simple directed graph with successor sets, transitive closure, inversion
// and reachability queries, used throughout HermiT (e.g. for role and concept
// hierarchies).

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::Hash;
use std::sync::OnceLock;

#[derive(Debug)]
pub struct Graph<T: Eq + Hash + Clone> {
    elements: HashSet<T>,
    successors_by_nodes: HashMap<T, HashSet<T>>,
    /// Lazily-initialised shared empty set, returned by [`Graph::successors`]
    /// for nodes with no successor entry (mirrors `Collections.emptySet()`).
    empty: OnceLock<HashSet<T>>,
}

// Hand-written Clone mirrors Graph.java:86-95: rebuild via add_edge so that
// keys whose successor sets are empty are never copied into the clone's map.
impl<T: Eq + Hash + Clone> Clone for Graph<T> {
    fn clone(&self) -> Self {
        let mut result = Graph::new();
        result.elements.extend(self.elements.iter().cloned());
        for (from, successors) in &self.successors_by_nodes {
            for successor in successors {
                result.add_edge(from.clone(), successor.clone());
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
            successors_by_nodes: HashMap::new(),
            empty: OnceLock::new(),
        }
    }

    pub fn add_edge(&mut self, from: T, to: T) {
        self.successors_by_nodes
            .entry(from.clone())
            .or_default()
            .insert(to.clone());
        self.elements.insert(from);
        self.elements.insert(to);
    }

    pub fn add_edges(&mut self, from: T, to: &HashSet<T>) {
        let successors = self.successors_by_nodes.entry(from.clone()).or_default();
        for t in to {
            successors.insert(t.clone());
        }
        self.elements.insert(from);
        for t in to {
            self.elements.insert(t.clone());
        }
    }

    pub fn get_elements(&self) -> &HashSet<T> {
        &self.elements
    }

    /// Faithful port of `Graph.getSuccessors`: returns a borrow of the live
    /// successor set (Java returns the set stored in `m_successorsByNodes`, or
    /// `Collections.emptySet()` when the node has no entry). The empty fallback
    /// borrows a shared empty set, so no allocation/clone occurs.
    pub fn successors(&self, node: &T) -> &HashSet<T> {
        self.successors_by_nodes
            .get(node)
            .unwrap_or_else(|| self.empty_successors())
    }

    /// Borrow of a shared empty successor set used by [`Graph::successors`] for
    /// nodes with no outgoing edges (mirrors `Collections.emptySet()`).
    fn empty_successors(&self) -> &HashSet<T> {
        self.empty.get_or_init(HashSet::new)
    }

    /// Cloning shim kept for external callers that consume an owned set; new
    /// code should prefer [`Graph::successors`] which mirrors Java by borrowing.
    pub fn get_successors(&self, node: &T) -> HashSet<T> {
        self.successors(node).clone()
    }

    pub fn transitively_close(&mut self) {
        let keys: Vec<T> = self.successors_by_nodes.keys().cloned().collect();
        for key in keys {
            let mut reachable = self.successors_by_nodes[&key].clone();
            let mut to_process: Vec<T> = reachable.iter().cloned().collect();
            while let Some(element_on_path) = to_process.pop() {
                if let Some(successors) = self.successors_by_nodes.get(&element_on_path) {
                    for successor in successors.clone() {
                        if reachable.insert(successor.clone()) {
                            to_process.push(successor);
                        }
                    }
                }
            }
            self.successors_by_nodes.insert(key, reachable);
        }
    }

    pub fn get_inverse(&self) -> Graph<T> {
        let mut result = Graph::new();
        for (from, successors) in &self.successors_by_nodes {
            for successor in successors {
                result.add_edge(successor.clone(), from.clone());
            }
        }
        result
    }

    pub fn remove_elements(&mut self, elements: &HashSet<T>) {
        for element in elements {
            self.elements.remove(element);
            self.successors_by_nodes.remove(element);
        }
    }

    pub fn is_reachable_successor(&self, from_node: &T, to_node: &T) -> bool {
        if from_node == to_node {
            return true;
        }
        let mut result: HashSet<T> = HashSet::new();
        let mut to_visit: VecDeque<T> = VecDeque::new();
        to_visit.push_back(from_node.clone());
        while let Some(current) = to_visit.pop_front() {
            let successors = self.successors(&current);
            if successors.contains(to_node) {
                return true;
            }
            if result.insert(current) {
                for successor in successors {
                    to_visit.push_back(successor.clone());
                }
            }
        }
        false
    }

    /// Remove `to_remove` from `node`'s successor set (no-op for absent edges).
    pub fn remove_successors(&mut self, node: &T, to_remove: &HashSet<T>) {
        if let Some(successors) = self.successors_by_nodes.get_mut(node) {
            for r in to_remove {
                successors.remove(r);
            }
        }
    }

    /// Remove a single edge `node -> successor`.
    pub fn remove_edge(&mut self, node: &T, successor: &T) {
        if let Some(successors) = self.successors_by_nodes.get_mut(node) {
            successors.remove(successor);
        }
    }

    /// Clear all of `node`'s outgoing edges.
    pub fn clear_successors(&mut self, node: &T) {
        if let Some(successors) = self.successors_by_nodes.get_mut(node) {
            successors.clear();
        }
    }

    pub fn get_reachable_successors(&self, from_node: &T) -> HashSet<T> {
        let mut result: HashSet<T> = HashSet::new();
        let mut to_visit: VecDeque<T> = VecDeque::new();
        to_visit.push_back(from_node.clone());
        while let Some(current) = to_visit.pop_front() {
            if result.insert(current.clone()) {
                for successor in self.successors(&current) {
                    to_visit.push_back(successor.clone());
                }
            }
        }
        result
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
            if let Some(successors) = self.successors_by_nodes.get(element) {
                for successor in successors {
                    if first_successor {
                        first_successor = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{successor}")?;
                }
            }
            writeln!(f, " }}")?;
        }
        Ok(())
    }
}
