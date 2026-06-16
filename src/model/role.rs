// Ports of org.semanticweb.HermiT.model.{Role,AtomicRole,InverseRole,NegatedAtomicRole}.

use std::sync::OnceLock;

use crate::model::atom::Atom;
use crate::model::predicate::DLPredicate;
use crate::model::term::Term;
use crate::prefixes::Prefixes;
use crate::{impl_display_prefixes, interned};

// ---------------------------------------------------------------------------
// AtomicRole
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct AtomicRoleData {
    iri: String,
}

interned!(pub AtomicRole => AtomicRoleData);

impl AtomicRole {
    pub fn create(iri: impl Into<String>) -> AtomicRole {
        AtomicRole::intern(AtomicRoleData { iri: iri.into() })
    }
    pub fn iri(&self) -> &str {
        &self.0.iri
    }
    pub fn arity(&self) -> usize {
        2
    }
    pub fn get_inverse(&self) -> Role {
        if self == AtomicRole::top_object_role() || self == AtomicRole::bottom_object_role() {
            Role::AtomicRole(self.clone())
        } else {
            Role::InverseRole(InverseRole::create(self.clone()))
        }
    }
    pub fn get_role_assertion(&self, term0: Term, term1: Term) -> Atom {
        Atom::create(DLPredicate::AtomicRole(self.clone()), vec![term0, term1])
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        prefixes.abbreviate_iri(&self.0.iri)
    }

    pub fn top_object_role() -> &'static AtomicRole {
        static R: OnceLock<AtomicRole> = OnceLock::new();
        R.get_or_init(|| AtomicRole::create("http://www.w3.org/2002/07/owl#topObjectProperty"))
    }
    pub fn bottom_object_role() -> &'static AtomicRole {
        static R: OnceLock<AtomicRole> = OnceLock::new();
        R.get_or_init(|| AtomicRole::create("http://www.w3.org/2002/07/owl#bottomObjectProperty"))
    }
    pub fn top_data_role() -> &'static AtomicRole {
        static R: OnceLock<AtomicRole> = OnceLock::new();
        R.get_or_init(|| AtomicRole::create("http://www.w3.org/2002/07/owl#topDataProperty"))
    }
    pub fn bottom_data_role() -> &'static AtomicRole {
        static R: OnceLock<AtomicRole> = OnceLock::new();
        R.get_or_init(|| AtomicRole::create("http://www.w3.org/2002/07/owl#bottomDataProperty"))
    }
}

// Ordering by IRI, mirroring DLOntology.AtomicRoleComparator.
impl PartialOrd for AtomicRole {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for AtomicRole {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        crate::model::java_string_cmp(self.iri(), other.iri())
    }
}

// ---------------------------------------------------------------------------
// InverseRole
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct InverseRoleData {
    inverse_of: AtomicRole,
}

interned!(pub InverseRole => InverseRoleData);

impl InverseRole {
    pub fn create(inverse_of: AtomicRole) -> InverseRole {
        InverseRole::intern(InverseRoleData { inverse_of })
    }
    pub fn get_inverse_of(&self) -> &AtomicRole {
        &self.0.inverse_of
    }
    pub fn get_inverse(&self) -> Role {
        Role::AtomicRole(self.0.inverse_of.clone())
    }
    pub fn get_role_assertion(&self, term0: Term, term1: Term) -> Atom {
        // Arguments are swapped: inv(r)(t0,t1) holds iff r(t1,t0).
        Atom::create(
            DLPredicate::AtomicRole(self.0.inverse_of.clone()),
            vec![term1, term0],
        )
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        format!("inv({})", self.0.inverse_of.to_string_prefixes(prefixes))
    }
}

// ---------------------------------------------------------------------------
// NegatedAtomicRole
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct NegatedAtomicRoleData {
    negated_atomic_role: AtomicRole,
}

interned!(pub NegatedAtomicRole => NegatedAtomicRoleData);

impl NegatedAtomicRole {
    pub fn create(negated_atomic_role: AtomicRole) -> NegatedAtomicRole {
        NegatedAtomicRole::intern(NegatedAtomicRoleData { negated_atomic_role })
    }
    pub fn get_negated_atomic_role(&self) -> &AtomicRole {
        &self.0.negated_atomic_role
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        format!("not({})", self.0.negated_atomic_role.to_string_prefixes(prefixes))
    }
}

// ---------------------------------------------------------------------------
// Role (abstract supertype)
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Role {
    AtomicRole(AtomicRole),
    InverseRole(InverseRole),
}

impl Role {
    pub fn get_inverse(&self) -> Role {
        match self {
            Role::AtomicRole(r) => r.get_inverse(),
            Role::InverseRole(r) => r.get_inverse(),
        }
    }
    pub fn get_role_assertion(&self, term0: Term, term1: Term) -> Atom {
        match self {
            Role::AtomicRole(r) => r.get_role_assertion(term0, term1),
            Role::InverseRole(r) => r.get_role_assertion(term0, term1),
        }
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        match self {
            Role::AtomicRole(r) => r.to_string_prefixes(prefixes),
            Role::InverseRole(r) => r.to_string_prefixes(prefixes),
        }
    }
}

impl From<AtomicRole> for Role {
    fn from(r: AtomicRole) -> Role {
        Role::AtomicRole(r)
    }
}
impl From<InverseRole> for Role {
    fn from(r: InverseRole) -> Role {
        Role::InverseRole(r)
    }
}

impl_display_prefixes!(AtomicRole, InverseRole, NegatedAtomicRole, Role);
