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

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TableauObject {
    Concept(Concept),
    DLPredicate(DLPredicate),
    NegatedAtomicRole(NegatedAtomicRole),
    DescriptionGraph(DescriptionGraph),
    Node(NodeId),
}

impl TableauObject {
    /// A cheap raw integer key uniquely identifying this object, consistent with
    /// `Eq`/`Hash` (equal objects -> equal keys). The label variants delegate to
    /// the interned-pointer-based `raw_key()` of their inner value; `Node` uses
    /// its (already small-integer) id. This lets the hot tuple-index hash avoid
    /// constructing a hasher and dispatching the derived `Hash` per call -- Java
    /// HermiT likewise caches `object.hashCode()` rather than rehashing.
    #[inline]
    pub fn raw_key(&self) -> usize {
        match self {
            TableauObject::Concept(c) => c.raw_key().wrapping_mul(5),
            TableauObject::DLPredicate(p) => p.raw_key().wrapping_mul(7),
            TableauObject::NegatedAtomicRole(r) => r.intern_ptr().wrapping_mul(11),
            TableauObject::DescriptionGraph(g) => g.intern_ptr().wrapping_mul(13),
            TableauObject::Node(id) => id.wrapping_mul(17),
        }
    }

    /// A *collision-free* 64-bit key: equal objects -> equal keys AND distinct
    /// objects -> distinct keys (unlike `raw_key`, whose `*5/*7/...` variant
    /// spreading can alias across variants). The inner per-value id is interned (a
    /// heap address < 2^48) or a small node id, so it fits in the low 61 bits; the
    /// 3-bit variant tag goes in the top bits. This exactness lets the tuple index
    /// match a trie edge on `(parent, unique_key)` ALONE -- never storing or
    /// dereferencing the object to confirm -- since two distinct objects can never
    /// share a key. (The binary table's column 0 genuinely mixes `Concept` and
    /// `DLPredicate`, so cross-variant exactness is required, not just per-variant.)
    #[inline]
    pub fn unique_key(&self) -> u64 {
        let (tag, inner): (u64, u64) = match self {
            TableauObject::Concept(c) => (0, c.raw_key() as u64),
            TableauObject::DLPredicate(p) => (1, p.raw_key() as u64),
            TableauObject::NegatedAtomicRole(r) => (2, r.intern_ptr() as u64),
            TableauObject::DescriptionGraph(g) => (3, g.intern_ptr() as u64),
            TableauObject::Node(id) => (4, *id as u64),
        };
        debug_assert!(inner < (1u64 << 61), "interned id does not fit in 61 bits");
        (tag << 61) | (inner & ((1u64 << 61) - 1))
    }

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
