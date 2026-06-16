// Port of the OWL-API `org.semanticweb.owlapi.reasoner.{Node, NodeSet}` shapes that
// HermiT's `Reasoner` getters return. A `Node<E>` groups entities HermiT
// treats as indistinguishable -- mutually-equivalent classes / object- or
// data-properties, or same-individuals under `IndividualNodeSetPolicy::BySameAs`. A
// `NodeSet<E>` is a set of such nodes.
//
// The crate's flat `HashSet`-returning getters (e.g. `sub_classes`) remain as a
// membership-faithful convenience; the `*_nodes` getters return these grouped shapes,
// preserving the equivalence / same-as partitioning that Java's `NodeSet` carries and
// the flat sets drop.

use std::collections::HashSet;
use std::hash::Hash;

/// A set of entities HermiT cannot tell apart (Java `Node<E>`): mutually-equivalent
/// classes/properties, or same-individuals. Order-independent.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Node<E: Eq + Hash> {
    entities: HashSet<E>,
}

impl<E: Eq + Hash + Clone> Node<E> {
    pub fn new(entities: HashSet<E>) -> Self {
        Node { entities }
    }
    pub fn singleton(entity: E) -> Self {
        Node { entities: std::iter::once(entity).collect() }
    }
    /// The grouped entities (Java `Node.getEntities`).
    pub fn entities(&self) -> &HashSet<E> {
        &self.entities
    }
    pub fn into_entities(self) -> HashSet<E> {
        self.entities
    }
    pub fn contains(&self, entity: &E) -> bool {
        self.entities.contains(entity)
    }
    pub fn is_empty(&self) -> bool {
        self.entities.is_empty()
    }
    /// Number of entities in the node (Java `Node.getSize`).
    pub fn len(&self) -> usize {
        self.entities.len()
    }
}

/// A set of [`Node`]s (Java `NodeSet<E>`).
#[derive(Debug, Clone, Default)]
pub struct NodeSet<E: Eq + Hash> {
    nodes: Vec<Node<E>>,
}

impl<E: Eq + Hash + Clone> NodeSet<E> {
    pub fn new(nodes: Vec<Node<E>>) -> Self {
        NodeSet { nodes }
    }
    /// The nodes (Java `NodeSet.getNodes`).
    pub fn nodes(&self) -> &[Node<E>] {
        &self.nodes
    }
    pub fn iter(&self) -> std::slice::Iter<'_, Node<E>> {
        self.nodes.iter()
    }
    /// Number of nodes (NOT entities) -- Java `NodeSet.getNodes().size()`.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
    /// Whether some node contains `entity` (Java `NodeSet.containsEntity`).
    pub fn contains(&self, entity: &E) -> bool {
        self.nodes.iter().any(|n| n.contains(entity))
    }
    /// The flattened entity set across all nodes (Java `NodeSet.getFlattened`) --
    /// equals what the crate's flat getter returns.
    pub fn flattened(&self) -> HashSet<E> {
        self.nodes.iter().flat_map(|n| n.entities().iter().cloned()).collect()
    }
}

impl<E: Eq + Hash + Clone> IntoIterator for NodeSet<E> {
    type Item = Node<E>;
    type IntoIter = std::vec::IntoIter<Node<E>>;
    fn into_iter(self) -> Self::IntoIter {
        self.nodes.into_iter()
    }
}

/// Partition `elements` into [`Node`]s by an equivalence relation given as a function
/// from an element to its full equivalence set (e.g. `Hierarchy::equivalent_elements_of`
/// for classes/properties, or `get_same_individuals` for individuals). Each returned
/// node is the intersection of an element's equivalence set with `elements`, so the
/// partition covers exactly `elements` with no element appearing twice.
pub fn group_by_equivalence<E, F>(elements: HashSet<E>, mut equivalents_of: F) -> NodeSet<E>
where
    E: Eq + Hash + Clone,
    F: FnMut(&E) -> HashSet<E>,
{
    let mut seen: HashSet<E> = HashSet::new();
    let mut nodes: Vec<Node<E>> = Vec::new();
    // Deterministic order is irrelevant to NodeSet semantics, but iterate a stable
    // snapshot so repeated runs group identically.
    for element in elements.iter() {
        if seen.contains(element) {
            continue;
        }
        // The node = this element's equivalence class restricted to `elements`.
        let mut group: HashSet<E> = equivalents_of(element)
            .into_iter()
            .filter(|e| elements.contains(e))
            .collect();
        group.insert(element.clone());
        for e in &group {
            seen.insert(e.clone());
        }
        nodes.push(Node::new(group));
    }
    NodeSet::new(nodes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn node_and_nodeset_basics() {
        let n = Node::new(["a", "b"].into_iter().collect());
        assert!(n.contains(&"a"));
        assert_eq!(n.len(), 2);
        let ns = NodeSet::new(vec![n, Node::singleton("c")]);
        assert_eq!(ns.len(), 2); // two nodes
        assert!(ns.contains(&"b"));
        assert!(ns.contains(&"c"));
        assert_eq!(ns.flattened().len(), 3); // three entities
    }

    #[test]
    fn group_by_equivalence_partitions() {
        // a≡b, c alone. elements = {a,b,c}.
        let elements: HashSet<&str> = ["a", "b", "c"].into_iter().collect();
        let ns = group_by_equivalence(elements, |e| {
            if *e == "a" || *e == "b" {
                ["a", "b"].into_iter().collect()
            } else {
                std::iter::once(*e).collect()
            }
        });
        assert_eq!(ns.len(), 2); // {a,b} and {c}
        assert!(ns.nodes().iter().any(|n| n.len() == 2 && n.contains(&"a") && n.contains(&"b")));
        assert!(ns.nodes().iter().any(|n| n.len() == 1 && n.contains(&"c")));
    }
}
