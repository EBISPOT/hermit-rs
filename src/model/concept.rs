// Ports of org.semanticweb.HermiT.model.{Concept,LiteralConcept,ExistentialConcept,
// AtomicConcept,AtomicNegationConcept,AtLeast,AtLeastConcept,AtLeastDataRange}.

use std::sync::OnceLock;

use crate::model::datarange::LiteralDataRange;
use crate::model::description_graph::ExistsDescriptionGraph;
use crate::model::role::Role;
use crate::prefixes::Prefixes;
use crate::{impl_display_prefixes, interned};

// ---------------------------------------------------------------------------
// AtomicConcept
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct AtomicConceptData {
    iri: String,
}

interned!(pub AtomicConcept => AtomicConceptData);

impl AtomicConcept {
    pub fn create(iri: impl Into<String>) -> AtomicConcept {
        AtomicConcept::intern(AtomicConceptData { iri: iri.into() })
    }
    pub fn iri(&self) -> &str {
        &self.0.iri
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn get_negation(&self) -> LiteralConcept {
        if self == AtomicConcept::thing() {
            LiteralConcept::AtomicConcept(AtomicConcept::nothing().clone())
        } else if self == AtomicConcept::nothing() {
            LiteralConcept::AtomicConcept(AtomicConcept::thing().clone())
        } else {
            LiteralConcept::AtomicNegationConcept(AtomicNegationConcept::create(self.clone()))
        }
    }
    pub fn is_always_true(&self) -> bool {
        self == AtomicConcept::thing()
    }
    pub fn is_always_false(&self) -> bool {
        self == AtomicConcept::nothing()
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        prefixes.abbreviate_iri(&self.0.iri)
    }

    pub fn thing() -> &'static AtomicConcept {
        static C: OnceLock<AtomicConcept> = OnceLock::new();
        C.get_or_init(|| AtomicConcept::create("http://www.w3.org/2002/07/owl#Thing"))
    }
    pub fn nothing() -> &'static AtomicConcept {
        static C: OnceLock<AtomicConcept> = OnceLock::new();
        C.get_or_init(|| AtomicConcept::create("http://www.w3.org/2002/07/owl#Nothing"))
    }
    pub fn internal_named() -> &'static AtomicConcept {
        static C: OnceLock<AtomicConcept> = OnceLock::new();
        C.get_or_init(|| AtomicConcept::create("internal:nam#Named"))
    }
}

// Ordering by IRI, mirroring DLOntology.AtomicConceptComparator (used for the
// deterministic TreeSet iteration in DLOntology).
impl PartialOrd for AtomicConcept {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for AtomicConcept {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        crate::model::java_string_cmp(self.iri(), other.iri())
    }
}

// ---------------------------------------------------------------------------
// AtomicNegationConcept
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct AtomicNegationConceptData {
    negated_atomic_concept: AtomicConcept,
}

interned!(pub AtomicNegationConcept => AtomicNegationConceptData);

impl AtomicNegationConcept {
    pub fn create(negated_atomic_concept: AtomicConcept) -> AtomicNegationConcept {
        AtomicNegationConcept::intern(AtomicNegationConceptData { negated_atomic_concept })
    }
    pub fn get_negated_atomic_concept(&self) -> &AtomicConcept {
        &self.0.negated_atomic_concept
    }
    pub fn get_negation(&self) -> LiteralConcept {
        LiteralConcept::AtomicConcept(self.0.negated_atomic_concept.clone())
    }
    pub fn is_always_true(&self) -> bool {
        self.0.negated_atomic_concept.is_always_false()
    }
    pub fn is_always_false(&self) -> bool {
        self.0.negated_atomic_concept.is_always_true()
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        format!("not({})", self.0.negated_atomic_concept.to_string_prefixes(prefixes))
    }
}

// ---------------------------------------------------------------------------
// AtLeastConcept
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct AtLeastConceptData {
    number: i32,
    on_role: Role,
    to_concept: LiteralConcept,
}

interned!(pub AtLeastConcept => AtLeastConceptData);

impl AtLeastConcept {
    pub fn create(number: i32, on_role: Role, to_concept: LiteralConcept) -> AtLeastConcept {
        AtLeastConcept::intern(AtLeastConceptData { number, on_role, to_concept })
    }
    pub fn number(&self) -> i32 {
        self.0.number
    }
    pub fn on_role(&self) -> &Role {
        &self.0.on_role
    }
    pub fn to_concept(&self) -> &LiteralConcept {
        &self.0.to_concept
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn is_always_true(&self) -> bool {
        false
    }
    pub fn is_always_false(&self) -> bool {
        self.0.to_concept.is_always_false()
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        format!(
            "atLeast({} {} {})",
            self.0.number,
            self.0.on_role.to_string_prefixes(prefixes),
            self.0.to_concept.to_string_prefixes(prefixes)
        )
    }
}

// ---------------------------------------------------------------------------
// AtLeastDataRange
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct AtLeastDataRangeData {
    number: i32,
    on_role: Role,
    to_data_range: LiteralDataRange,
}

interned!(pub AtLeastDataRange => AtLeastDataRangeData);

impl AtLeastDataRange {
    pub fn create(number: i32, on_role: Role, to_data_range: LiteralDataRange) -> AtLeastDataRange {
        AtLeastDataRange::intern(AtLeastDataRangeData { number, on_role, to_data_range })
    }
    pub fn number(&self) -> i32 {
        self.0.number
    }
    pub fn on_role(&self) -> &Role {
        &self.0.on_role
    }
    pub fn to_data_range(&self) -> &LiteralDataRange {
        &self.0.to_data_range
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn is_always_true(&self) -> bool {
        false
    }
    pub fn is_always_false(&self) -> bool {
        self.0.to_data_range.is_always_false()
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        format!(
            "atLeast({} {} {})",
            self.0.number,
            self.0.on_role.to_string_prefixes(prefixes),
            self.0.to_data_range.to_string_prefixes(prefixes)
        )
    }
}

// ---------------------------------------------------------------------------
// LiteralConcept (abstract): atomic concept or negation of an atomic concept
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum LiteralConcept {
    AtomicConcept(AtomicConcept),
    AtomicNegationConcept(AtomicNegationConcept),
}

impl LiteralConcept {
    pub fn get_negation(&self) -> LiteralConcept {
        match self {
            LiteralConcept::AtomicConcept(c) => c.get_negation(),
            LiteralConcept::AtomicNegationConcept(c) => c.get_negation(),
        }
    }
    pub fn is_always_true(&self) -> bool {
        match self {
            LiteralConcept::AtomicConcept(c) => c.is_always_true(),
            LiteralConcept::AtomicNegationConcept(c) => c.is_always_true(),
        }
    }
    pub fn is_always_false(&self) -> bool {
        match self {
            LiteralConcept::AtomicConcept(c) => c.is_always_false(),
            LiteralConcept::AtomicNegationConcept(c) => c.is_always_false(),
        }
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        match self {
            LiteralConcept::AtomicConcept(c) => c.to_string_prefixes(prefixes),
            LiteralConcept::AtomicNegationConcept(c) => c.to_string_prefixes(prefixes),
        }
    }
}

impl From<AtomicConcept> for LiteralConcept {
    fn from(c: AtomicConcept) -> LiteralConcept {
        LiteralConcept::AtomicConcept(c)
    }
}
impl From<AtomicNegationConcept> for LiteralConcept {
    fn from(c: AtomicNegationConcept) -> LiteralConcept {
        LiteralConcept::AtomicNegationConcept(c)
    }
}

// ---------------------------------------------------------------------------
// ExistentialConcept (abstract): at-least concepts (and description graphs)
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ExistentialConcept {
    AtLeastConcept(AtLeastConcept),
    AtLeastDataRange(AtLeastDataRange),
    ExistsDescriptionGraph(ExistsDescriptionGraph),
}

impl ExistentialConcept {
    pub fn is_always_true(&self) -> bool {
        false
    }
    pub fn is_always_false(&self) -> bool {
        match self {
            ExistentialConcept::AtLeastConcept(c) => c.is_always_false(),
            ExistentialConcept::AtLeastDataRange(c) => c.is_always_false(),
            ExistentialConcept::ExistsDescriptionGraph(c) => c.is_always_false(),
        }
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        match self {
            ExistentialConcept::AtLeastConcept(c) => c.to_string_prefixes(prefixes),
            ExistentialConcept::AtLeastDataRange(c) => c.to_string_prefixes(prefixes),
            ExistentialConcept::ExistsDescriptionGraph(c) => c.to_string_prefixes(prefixes),
        }
    }
}

// ---------------------------------------------------------------------------
// Concept (abstract supertype)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Concept {
    AtomicConcept(AtomicConcept),
    AtomicNegationConcept(AtomicNegationConcept),
    AtLeastConcept(AtLeastConcept),
    AtLeastDataRange(AtLeastDataRange),
    ExistsDescriptionGraph(ExistsDescriptionGraph),
}

impl Concept {
    pub fn is_always_true(&self) -> bool {
        match self {
            Concept::AtomicConcept(c) => c.is_always_true(),
            Concept::AtomicNegationConcept(c) => c.is_always_true(),
            Concept::AtLeastConcept(c) => c.is_always_true(),
            Concept::AtLeastDataRange(c) => c.is_always_true(),
            Concept::ExistsDescriptionGraph(c) => c.is_always_true(),
        }
    }
    pub fn is_always_false(&self) -> bool {
        match self {
            Concept::AtomicConcept(c) => c.is_always_false(),
            Concept::AtomicNegationConcept(c) => c.is_always_false(),
            Concept::AtLeastConcept(c) => c.is_always_false(),
            Concept::AtLeastDataRange(c) => c.is_always_false(),
            Concept::ExistsDescriptionGraph(c) => c.is_always_false(),
        }
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        match self {
            Concept::AtomicConcept(c) => c.to_string_prefixes(prefixes),
            Concept::AtomicNegationConcept(c) => c.to_string_prefixes(prefixes),
            Concept::AtLeastConcept(c) => c.to_string_prefixes(prefixes),
            Concept::AtLeastDataRange(c) => c.to_string_prefixes(prefixes),
            Concept::ExistsDescriptionGraph(c) => c.to_string_prefixes(prefixes),
        }
    }
}

impl From<LiteralConcept> for Concept {
    fn from(c: LiteralConcept) -> Concept {
        match c {
            LiteralConcept::AtomicConcept(c) => Concept::AtomicConcept(c),
            LiteralConcept::AtomicNegationConcept(c) => Concept::AtomicNegationConcept(c),
        }
    }
}
impl From<ExistentialConcept> for Concept {
    fn from(c: ExistentialConcept) -> Concept {
        match c {
            ExistentialConcept::AtLeastConcept(c) => Concept::AtLeastConcept(c),
            ExistentialConcept::AtLeastDataRange(c) => Concept::AtLeastDataRange(c),
            ExistentialConcept::ExistsDescriptionGraph(c) => Concept::ExistsDescriptionGraph(c),
        }
    }
}

impl_display_prefixes!(
    AtomicConcept,
    AtomicNegationConcept,
    AtLeastConcept,
    AtLeastDataRange,
    LiteralConcept,
    ExistentialConcept,
    Concept,
);
