// Ports of org.semanticweb.HermiT.model.{DLPredicate,Equality,Inequality,
// AnnotatedEquality,NodeIDLessEqualThan,NodeIDsAscendingOrEqual} and the
// DLPredicate-implementing model classes gathered into one dispatch enum.

use crate::model::concept::{AtLeastConcept, AtLeastDataRange, AtomicConcept, LiteralConcept};
use crate::model::datarange::{
    AtomicNegationDataRange, ConstantEnumeration, DatatypeRestriction, InternalDatatype,
};
use crate::model::description_graph::{DescriptionGraph, ExistsDescriptionGraph};
use crate::model::role::{AtomicRole, Role};
use crate::prefixes::Prefixes;
use crate::{impl_display_prefixes, interned};

// ---------------------------------------------------------------------------
// AnnotatedEquality
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct AnnotatedEqualityData {
    cardinality: i32,
    on_role: Role,
    to_concept: LiteralConcept,
}

interned!(pub AnnotatedEquality => AnnotatedEqualityData);

impl AnnotatedEquality {
    pub fn create(cardinality: i32, on_role: Role, to_concept: LiteralConcept) -> AnnotatedEquality {
        AnnotatedEquality::intern(AnnotatedEqualityData { cardinality, on_role, to_concept })
    }
    pub fn cardinality(&self) -> i32 {
        self.0.cardinality
    }
    pub fn on_role(&self) -> &Role {
        &self.0.on_role
    }
    pub fn to_concept(&self) -> &LiteralConcept {
        &self.0.to_concept
    }
    pub fn arity(&self) -> usize {
        3
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        format!(
            "==@atMost({} {} {})",
            self.0.cardinality,
            self.0.on_role.to_string_prefixes(prefixes),
            self.0.to_concept.to_string_prefixes(prefixes)
        )
    }
}

// ---------------------------------------------------------------------------
// NodeIDsAscendingOrEqual
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct NodeIDsAscendingOrEqualData {
    arity: usize,
}

interned!(pub NodeIDsAscendingOrEqual => NodeIDsAscendingOrEqualData);

impl NodeIDsAscendingOrEqual {
    pub fn create(arity: usize) -> NodeIDsAscendingOrEqual {
        NodeIDsAscendingOrEqual::intern(NodeIDsAscendingOrEqualData { arity })
    }
    pub fn arity(&self) -> usize {
        self.0.arity
    }
    pub fn to_string_prefixes(&self, _prefixes: &Prefixes) -> String {
        "NodeIDsAscendingOrEqual".to_string()
    }
}

impl_display_prefixes!(AnnotatedEquality, NodeIDsAscendingOrEqual);

// ---------------------------------------------------------------------------
// DLPredicate (the `DLPredicate` interface, as a closed dispatch enum)
// ---------------------------------------------------------------------------
//
// The unit variants Equality / Inequality / NodeIDLessEqualThan correspond to
// the Java singleton predicates (their `INSTANCE` constants).

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum DLPredicate {
    AtomicConcept(AtomicConcept),
    AtomicRole(AtomicRole),
    AtLeastConcept(AtLeastConcept),
    AtLeastDataRange(AtLeastDataRange),
    Equality,
    Inequality,
    AnnotatedEquality(AnnotatedEquality),
    NodeIdLessEqualThan,
    NodeIDsAscendingOrEqual(NodeIDsAscendingOrEqual),
    DatatypeRestriction(DatatypeRestriction),
    ConstantEnumeration(ConstantEnumeration),
    InternalDatatype(InternalDatatype),
    AtomicNegationDataRange(AtomicNegationDataRange),
    DescriptionGraph(DescriptionGraph),
    ExistsDescriptionGraph(ExistsDescriptionGraph),
}

impl DLPredicate {
    pub fn arity(&self) -> usize {
        match self {
            DLPredicate::AtomicConcept(p) => p.arity(),
            DLPredicate::AtomicRole(p) => p.arity(),
            DLPredicate::AtLeastConcept(p) => p.arity(),
            DLPredicate::AtLeastDataRange(p) => p.arity(),
            DLPredicate::Equality => 2,
            DLPredicate::Inequality => 2,
            DLPredicate::AnnotatedEquality(p) => p.arity(),
            DLPredicate::NodeIdLessEqualThan => 2,
            DLPredicate::NodeIDsAscendingOrEqual(p) => p.arity(),
            DLPredicate::DatatypeRestriction(p) => p.arity(),
            DLPredicate::ConstantEnumeration(p) => p.arity(),
            DLPredicate::InternalDatatype(p) => p.arity(),
            DLPredicate::AtomicNegationDataRange(p) => p.arity(),
            DLPredicate::DescriptionGraph(p) => p.arity(),
            DLPredicate::ExistsDescriptionGraph(p) => p.arity(),
        }
    }

    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        match self {
            DLPredicate::AtomicConcept(p) => p.to_string_prefixes(prefixes),
            DLPredicate::AtomicRole(p) => p.to_string_prefixes(prefixes),
            DLPredicate::AtLeastConcept(p) => p.to_string_prefixes(prefixes),
            DLPredicate::AtLeastDataRange(p) => p.to_string_prefixes(prefixes),
            DLPredicate::Equality => "==".to_string(),
            DLPredicate::Inequality => "!=".to_string(),
            DLPredicate::AnnotatedEquality(p) => p.to_string_prefixes(prefixes),
            DLPredicate::NodeIdLessEqualThan => "<=".to_string(),
            DLPredicate::NodeIDsAscendingOrEqual(p) => p.to_string_prefixes(prefixes),
            DLPredicate::DatatypeRestriction(p) => p.to_string_prefixes(prefixes),
            DLPredicate::ConstantEnumeration(p) => p.to_string_prefixes(prefixes),
            DLPredicate::InternalDatatype(p) => p.to_string_prefixes(prefixes),
            DLPredicate::AtomicNegationDataRange(p) => p.to_string_prefixes(prefixes),
            DLPredicate::DescriptionGraph(p) => p.to_string_prefixes(prefixes),
            DLPredicate::ExistsDescriptionGraph(p) => p.to_string_prefixes(prefixes),
        }
    }

    /// Port of `Equality.toOrderedString(Prefixes)`. In Java only the
    /// `Equality` predicate defines `toOrderedString`, which simply delegates
    /// to `toString(prefixes)` (yielding `"=="`). Provided for parity; like the
    /// Java method it is otherwise unused.
    pub fn to_ordered_string(&self, prefixes: &Prefixes) -> String {
        // Mirrors Equality.toOrderedString == Equality.toString.
        self.to_string_prefixes(prefixes)
    }

    /// `m_dlPredicate instanceof AtLeast`.
    pub fn is_at_least(&self) -> bool {
        matches!(
            self,
            DLPredicate::AtLeastConcept(_) | DLPredicate::AtLeastDataRange(_)
        )
    }
    /// `predicate instanceof LiteralConcept` -- among DLPredicates only
    /// AtomicConcept is also a LiteralConcept.
    pub fn is_literal_concept(&self) -> bool {
        matches!(self, DLPredicate::AtomicConcept(_))
    }
    pub fn is_atomic_concept(&self) -> bool {
        matches!(self, DLPredicate::AtomicConcept(_))
    }
    pub fn is_equality(&self) -> bool {
        matches!(self, DLPredicate::Equality)
    }
    pub fn is_annotated_equality(&self) -> bool {
        matches!(self, DLPredicate::AnnotatedEquality(_))
    }
    pub fn is_node_id_less_equal_than(&self) -> bool {
        matches!(self, DLPredicate::NodeIdLessEqualThan)
    }
    pub fn is_node_ids_ascending_or_equal(&self) -> bool {
        matches!(self, DLPredicate::NodeIDsAscendingOrEqual(_))
    }
    /// `predicate instanceof DataRange` -- the LiteralDataRange-implementing
    /// predicates.
    pub fn is_data_range(&self) -> bool {
        matches!(
            self,
            DLPredicate::DatatypeRestriction(_)
                | DLPredicate::ConstantEnumeration(_)
                | DLPredicate::InternalDatatype(_)
                | DLPredicate::AtomicNegationDataRange(_)
        )
    }
    /// `predicate instanceof Role` -- among DLPredicates only AtomicRole is a
    /// Role (InverseRole does not implement DLPredicate).
    pub fn is_role(&self) -> bool {
        matches!(self, DLPredicate::AtomicRole(_))
    }
    pub fn as_atomic_concept(&self) -> Option<&AtomicConcept> {
        match self {
            DLPredicate::AtomicConcept(c) => Some(c),
            _ => None,
        }
    }
}

impl From<AtomicConcept> for DLPredicate {
    fn from(p: AtomicConcept) -> DLPredicate {
        DLPredicate::AtomicConcept(p)
    }
}
impl From<AtomicRole> for DLPredicate {
    fn from(p: AtomicRole) -> DLPredicate {
        DLPredicate::AtomicRole(p)
    }
}
impl From<AtLeastConcept> for DLPredicate {
    fn from(p: AtLeastConcept) -> DLPredicate {
        DLPredicate::AtLeastConcept(p)
    }
}
impl From<AtLeastDataRange> for DLPredicate {
    fn from(p: AtLeastDataRange) -> DLPredicate {
        DLPredicate::AtLeastDataRange(p)
    }
}
impl From<AnnotatedEquality> for DLPredicate {
    fn from(p: AnnotatedEquality) -> DLPredicate {
        DLPredicate::AnnotatedEquality(p)
    }
}
impl From<NodeIDsAscendingOrEqual> for DLPredicate {
    fn from(p: NodeIDsAscendingOrEqual) -> DLPredicate {
        DLPredicate::NodeIDsAscendingOrEqual(p)
    }
}
impl From<DescriptionGraph> for DLPredicate {
    fn from(p: DescriptionGraph) -> DLPredicate {
        DLPredicate::DescriptionGraph(p)
    }
}
impl From<ExistsDescriptionGraph> for DLPredicate {
    fn from(p: ExistsDescriptionGraph) -> DLPredicate {
        DLPredicate::ExistsDescriptionGraph(p)
    }
}

impl_display_prefixes!(DLPredicate);
