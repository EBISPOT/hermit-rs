// Port of the org.semanticweb.HermiT.model package: the description-logic data
// model (terms, concepts, roles, data ranges, predicates, atoms and DL clauses)
// shared by the structural transformation and the (hyper)tableau engine.
//
// Each leaf class is an interned, immutable value type (see `crate::intern`),
// and the abstract Java supertypes (Term, Concept, Role, DataRange, ...) are
// modelled as closed dispatch enums.

/// Orders two IRIs exactly as Java's `String.compareTo`, i.e. lexicographically
/// by UTF-16 code units. This matches the `AtomicConceptComparator` /
/// `AtomicRoleComparator` / `IndividualComparator` used for the deterministic
/// `TreeSet` iteration in `DLOntology`. It differs from Rust's default `str`
/// ordering (by Unicode scalar value) only for supplementary-plane characters.
pub(crate) fn java_string_cmp(a: &str, b: &str) -> std::cmp::Ordering {
    a.encode_utf16().cmp(b.encode_utf16())
}

pub mod atom;
pub mod clause;
pub mod concept;
pub mod datarange;
pub mod description_graph;
pub mod dl_ontology;
pub mod predicate;
pub mod role;
pub mod term;

pub use atom::Atom;
pub use clause::DLClause;
pub use concept::{
    AtLeastConcept, AtLeastDataRange, AtomicConcept, AtomicNegationConcept, Concept,
    ExistentialConcept, LiteralConcept,
};
pub use datarange::{
    AtomicDataRange, AtomicNegationDataRange, ConstantEnumeration, DatatypeRestriction,
    InternalDatatype, LiteralDataRange,
};
pub use description_graph::{DescriptionGraph, Edge, ExistsDescriptionGraph};
pub use dl_ontology::DLOntology;
pub use predicate::{AnnotatedEquality, DLPredicate, NodeIDsAscendingOrEqual};
pub use role::{AtomicRole, InverseRole, NegatedAtomicRole, Role};
pub use term::{Constant, Individual, Term, Variable};
