// The heterogeneous element type stored in the tableau's extension tables.
//
// HermiT stores `Object[]` tuples where position 0 is a concept or DL predicate
// (the label) and positions 1.. are `Node`s. Rust needs a concrete element
// type, so this enum unifies the label objects (kept as the existing `model`
// dispatch enums `Concept` / `DLPredicate`, plus `DescriptionGraph`) with node
// references. The binary (concept) tables put a `Concept` at position 0; the
// ternary (role/predicate) tables put a `DLPredicate` there.

use crate::model::{Concept, DLPredicate, DescriptionGraph, NegatedAtomicRole};
use crate::tableau::node::NodeId;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TableauObject {
    Concept(Concept),
    DLPredicate(DLPredicate),
    NegatedAtomicRole(NegatedAtomicRole),
    DescriptionGraph(DescriptionGraph),
    Node(NodeId),
}

impl TableauObject {
    pub fn as_node(&self) -> Option<NodeId> {
        match self {
            TableauObject::Node(id) => Some(*id),
            _ => None,
        }
    }
    pub fn is_node(&self) -> bool {
        matches!(self, TableauObject::Node(_))
    }
    pub fn as_concept(&self) -> Option<&Concept> {
        match self {
            TableauObject::Concept(c) => Some(c),
            _ => None,
        }
    }
    pub fn as_dl_predicate(&self) -> Option<&DLPredicate> {
        match self {
            TableauObject::DLPredicate(p) => Some(p),
            _ => None,
        }
    }
    pub fn as_description_graph(&self) -> Option<&DescriptionGraph> {
        match self {
            TableauObject::DescriptionGraph(g) => Some(g),
            _ => None,
        }
    }
    pub fn as_negated_atomic_role(&self) -> Option<&NegatedAtomicRole> {
        match self {
            TableauObject::NegatedAtomicRole(r) => Some(r),
            _ => None,
        }
    }
}

impl From<NegatedAtomicRole> for TableauObject {
    fn from(r: NegatedAtomicRole) -> Self {
        TableauObject::NegatedAtomicRole(r)
    }
}

impl From<Concept> for TableauObject {
    fn from(c: Concept) -> Self {
        TableauObject::Concept(c)
    }
}
impl From<DLPredicate> for TableauObject {
    fn from(p: DLPredicate) -> Self {
        TableauObject::DLPredicate(p)
    }
}
impl From<DescriptionGraph> for TableauObject {
    fn from(g: DescriptionGraph) -> Self {
        TableauObject::DescriptionGraph(g)
    }
}
