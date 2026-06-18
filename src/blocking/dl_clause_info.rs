// Port of the `DLClauseInfo` structural decomposition from
// org.semanticweb.HermiT.blocking.BlockingValidator.
//
// HermiT's validated blocking re-checks every general concept inclusion (GCI)
// clause against the model around a (candidate) blocked node. To do that it
// first decomposes each GCI clause into the variable structure HermiT's
// clausification guarantees: the body mentions a centre variable `X`, some
// successor variables `Y1..Yn` (each linked to `X` by exactly one role in one
// direction) and some `Z1..Zm` variables (concept-only). This module ports that
// decomposition (`DLClauseInfo`'s body parsing); the retrieval/consequence
// machinery that drives the actual validation is staged separately.
//
// This is a pure function of a `model::DLClause` and changes no reasoning
// behaviour; it is the foundation the `BlockingValidator` is built on.

use rustc_hash::FxHashMap as HashMap;

use crate::model::{AtomicConcept, AtomicRole, DLClause, DLPredicate, Variable};

/// Which decomposed variable an argument of a consequence atom refers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgumentType {
    XVar,
    YVar,
    ZVar,
}

/// A decomposed head atom of a GCI clause, used to check whether the clause's
/// consequence holds around a (candidate) blocked node. Mirrors HermiT's
/// `SimpleConsequenceAtom` / `X2YOrY2XConsequenceAtom` / `MirroredYConsequenceAtom`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConsequenceAtom {
    /// A plain tuple `predicate(args...)`, each argument given by its variable
    /// kind and the index into the clause's Y/Z variable list (X is index 0).
    Simple {
        predicate: DLPredicate,
        argument_types: Vec<ArgumentType>,
        argument_indexes: Vec<usize>,
    },
    /// A role between `X` and `Yi` whose "real X" is adjusted when `Yi` is the
    /// actual node's parent (the blocked-X case).
    X2YOrY2X {
        role: AtomicRole,
        y_argument_index: usize,
        is_x2y: bool,
    },
    /// A concept on `Yi`, checked on `Yi`'s blocker when `Yi` is blocked (the
    /// non-blocked-X mirroring case).
    MirroredY {
        concept: AtomicConcept,
        y_argument_index: usize,
    },
}

fn index_of(variables: &[Variable], variable: &Variable) -> Option<usize> {
    variables.iter().position(|v| v == variable)
}

/// The constraints a clause body places on one `Yi` successor variable: the
/// atomic concepts asserted on it, and the roles linking it to `X` in each
/// direction (`X → Yi` and `Yi → X`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YConstraint {
    pub y_concepts: Vec<AtomicConcept>,
    pub x2y_roles: Vec<AtomicRole>,
    pub y2x_roles: Vec<AtomicRole>,
}

/// The decomposed structure of a GCI clause, mirroring HermiT's `DLClauseInfo`
/// fields for the body (`m_xConcepts`, `m_x2xRoles`, `m_yVariables` /
/// `m_yConstraints`, `m_zVariables` / `m_zConcepts`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DLClauseInfo {
    pub x_concepts: Vec<AtomicConcept>,
    pub x2x_roles: Vec<AtomicRole>,
    pub y_variables: Vec<Variable>,
    pub y_constraints: Vec<YConstraint>,
    pub z_variables: Vec<Variable>,
    pub z_concepts: Vec<Vec<AtomicConcept>>,
    /// The clause's consequences specialized for the two cases the validator
    /// checks: when the centre node `X` is itself blocked, and when it is not.
    pub consequences_for_blocked_x: Vec<ConsequenceAtom>,
    pub consequences_for_nonblocked_x: Vec<ConsequenceAtom>,
}

/// Decomposes the head of a GCI clause into the per-case consequence atoms,
/// mirroring the head-parsing tail of HermiT's `DLClauseInfo` constructor.
fn parse_head(
    clause: &DLClause,
    y_variables: &[Variable],
    z_variables: &[Variable],
) -> (Vec<ConsequenceAtom>, Vec<ConsequenceAtom>) {
    let mut blocked: Vec<ConsequenceAtom> = Vec::new();
    let mut nonblocked: Vec<ConsequenceAtom> = Vec::new();

    let simple = |predicate: DLPredicate, types: Vec<ArgumentType>, indexes: Vec<usize>| {
        ConsequenceAtom::Simple { predicate, argument_types: types, argument_indexes: indexes }
    };

    for i in 0..clause.get_head_length() {
        let atom = clause.get_head_atom(i);
        let predicate = atom.get_dl_predicate().clone();
        let var1 = atom.get_argument_variable(0).expect("head argument 0 is a variable").clone();
        let is_x = |v: &Variable| v.name() == "X";

        match &predicate {
            DLPredicate::AtomicConcept(concept) => {
                // B(X) or B(Yi).
                let (arg_type, arg_index) = match index_of(y_variables, &var1) {
                    Some(idx) => (ArgumentType::YVar, idx),
                    None => (ArgumentType::XVar, 0),
                };
                let blocked_atom = simple(predicate.clone(), vec![arg_type], vec![arg_index]);
                let nonblocked_atom = if arg_type == ArgumentType::XVar {
                    blocked_atom.clone()
                } else {
                    ConsequenceAtom::MirroredY { concept: concept.clone(), y_argument_index: arg_index }
                };
                blocked.push(blocked_atom);
                nonblocked.push(nonblocked_atom);
            }
            DLPredicate::AtLeastConcept(_) => {
                // >= h S.B(X). (Java's BlockingValidator has no head branch for
                // AtLeastDataRange, so such a head atom yields no consequence.)
                let atom = simple(predicate.clone(), vec![ArgumentType::XVar], vec![0]);
                blocked.push(atom.clone());
                nonblocked.push(atom);
            }
            DLPredicate::Equality => {
                let var2 = atom.get_argument_variable(1).expect("equality argument 1").clone();
                let atom = if is_x(&var1) || is_x(&var2) {
                    // x == zi
                    let z = if is_x(&var1) { &var2 } else { &var1 };
                    let z_index = index_of(z_variables, z).expect("Z variable index");
                    simple(predicate.clone(), vec![ArgumentType::XVar, ArgumentType::ZVar], vec![0, z_index])
                } else if index_of(z_variables, &var1).is_some() || index_of(z_variables, &var2).is_some() {
                    // y == zi
                    let (y, z) = if index_of(z_variables, &var2).is_some() {
                        (&var1, &var2)
                    } else {
                        (&var2, &var1)
                    };
                    let y_index = index_of(y_variables, y).expect("Y variable index");
                    let z_index = index_of(z_variables, z).expect("Z variable index");
                    simple(predicate.clone(), vec![ArgumentType::YVar, ArgumentType::ZVar], vec![y_index, z_index])
                } else {
                    // yi == yj
                    let y1 = index_of(y_variables, &var1).expect("Y variable index");
                    let y2 = index_of(y_variables, &var2).expect("Y variable index");
                    simple(predicate.clone(), vec![ArgumentType::YVar, ArgumentType::YVar], vec![y1, y2])
                };
                blocked.push(atom.clone());
                nonblocked.push(atom);
            }
            DLPredicate::AnnotatedEquality(_) => {
                // (yi == yj) @^x_{<=h S.B} -- arity 3.
                let var2 = atom.get_argument_variable(1).expect("annotated equality argument 1").clone();
                let y1 = index_of(y_variables, &var1).expect("Y variable index");
                let y2 = index_of(y_variables, &var2).expect("Y variable index");
                let atom = simple(
                    predicate.clone(),
                    vec![ArgumentType::YVar, ArgumentType::YVar, ArgumentType::XVar],
                    vec![y1, y2, 0],
                );
                blocked.push(atom.clone());
                nonblocked.push(atom);
            }
            DLPredicate::AtomicRole(role) => {
                let var2 = atom.get_argument_variable(1).expect("role argument 1").clone();
                if is_x(&var1) && is_x(&var2) {
                    let atom = simple(
                        predicate.clone(),
                        vec![ArgumentType::XVar, ArgumentType::XVar],
                        vec![0, 0],
                    );
                    blocked.push(atom.clone());
                    nonblocked.push(atom);
                } else if is_x(&var1) {
                    // R(X, Yi) or R(X, Zj).
                    match index_of(y_variables, &var2) {
                        Some(y_index) => {
                            blocked.push(ConsequenceAtom::X2YOrY2X {
                                role: role.clone(),
                                y_argument_index: y_index,
                                is_x2y: true,
                            });
                            nonblocked.push(simple(
                                predicate.clone(),
                                vec![ArgumentType::XVar, ArgumentType::YVar],
                                vec![0, y_index],
                            ));
                        }
                        None => {
                            let z_index = index_of(z_variables, &var2).expect("Z variable index");
                            let atom = simple(
                                predicate.clone(),
                                vec![ArgumentType::XVar, ArgumentType::ZVar],
                                vec![0, z_index],
                            );
                            blocked.push(atom.clone());
                            nonblocked.push(atom);
                        }
                    }
                } else {
                    // R(Yi, X) or R(Zj, X).
                    match index_of(y_variables, &var1) {
                        Some(y_index) => {
                            blocked.push(ConsequenceAtom::X2YOrY2X {
                                role: role.clone(),
                                y_argument_index: y_index,
                                is_x2y: false,
                            });
                            nonblocked.push(simple(
                                predicate.clone(),
                                vec![ArgumentType::YVar, ArgumentType::XVar],
                                vec![y_index, 0],
                            ));
                        }
                        None => {
                            let z_index = index_of(z_variables, &var1).expect("Z variable index");
                            let atom = simple(
                                predicate.clone(),
                                vec![ArgumentType::ZVar, ArgumentType::XVar],
                                vec![z_index, 0],
                            );
                            blocked.push(atom.clone());
                            nonblocked.push(atom);
                        }
                    }
                }
            }
            _ => {}
        }
    }
    (blocked, nonblocked)
}

fn push_unique<T: PartialEq>(vec: &mut Vec<T>, value: T) {
    if !vec.contains(&value) {
        vec.push(value);
    }
}

impl DLClauseInfo {
    /// Decomposes the body of `clause` (which must be a GCI) into its X/Y/Z
    /// structure. Panics if the clause's premise mentions a variable other than
    /// `X`, `Yi`, `Zj`, mirroring HermiT's internal-error checks.
    pub fn new(clause: &DLClause) -> DLClauseInfo {
        let mut x_concepts: Vec<AtomicConcept> = Vec::new();
        let mut x2x_roles: Vec<AtomicRole> = Vec::new();
        // First-encounter order is preserved so the decomposition is
        // deterministic (HermiT uses HashSets, but the validation is order
        // independent).
        let mut y_variables: Vec<Variable> = Vec::new();
        let mut y2concepts: HashMap<Variable, Vec<AtomicConcept>> = HashMap::default();
        let mut x2y_roles: HashMap<Variable, Vec<AtomicRole>> = HashMap::default();
        let mut y2x_roles: HashMap<Variable, Vec<AtomicRole>> = HashMap::default();
        let mut z_variables: Vec<Variable> = Vec::new();
        let mut z2concepts: HashMap<Variable, Vec<AtomicConcept>> = HashMap::default();

        let ensure_y = |y_variables: &mut Vec<Variable>, var: &Variable| {
            if !y_variables.contains(var) {
                y_variables.push(var.clone());
            }
        };

        for i in 0..clause.get_body_length() {
            let atom = clause.get_body_atom(i);
            let predicate = atom.get_dl_predicate();
            let var1 = atom
                .get_argument_variable(0)
                .expect("clause premise atom argument 0 must be a variable")
                .clone();
            match predicate {
                DLPredicate::AtomicConcept(concept) => {
                    if var1.name() == "X" {
                        push_unique(&mut x_concepts, concept.clone());
                    } else if var1.name().starts_with('Y') {
                        ensure_y(&mut y_variables, &var1);
                        push_unique(y2concepts.entry(var1).or_default(), concept.clone());
                    } else if var1.name().starts_with('Z') {
                        if !z_variables.contains(&var1) {
                            z_variables.push(var1.clone());
                        }
                        push_unique(z2concepts.entry(var1).or_default(), concept.clone());
                    } else {
                        panic!(
                            "Internal error: clause premise contained a variable other than \
                             X, Yi, Zi in a concept atom."
                        );
                    }
                }
                DLPredicate::AtomicRole(role) => {
                    let var2 = atom
                        .get_argument_variable(1)
                        .expect("role atom argument 1 must be a variable")
                        .clone();
                    if var1.name() == "X" {
                        if var2.name() == "X" {
                            push_unique(&mut x2x_roles, role.clone());
                        } else if var2.name().starts_with('Y') {
                            ensure_y(&mut y_variables, &var2);
                            push_unique(x2y_roles.entry(var2).or_default(), role.clone());
                        } else {
                            panic!(
                                "Internal error: clause premise contains a role atom with \
                                 variables other than X and Yi."
                            );
                        }
                    } else if var2.name() == "X" {
                        if var1.name().starts_with('Y') {
                            ensure_y(&mut y_variables, &var1);
                            push_unique(y2x_roles.entry(var1).or_default(), role.clone());
                        } else {
                            panic!(
                                "Internal error: clause premise contains a role atom with \
                                 variables other than X and Yi."
                            );
                        }
                    } else {
                        panic!(
                            "Internal error: clause premise contained variables other than \
                             X and Yi in a role atom."
                        );
                    }
                }
                _ => {
                    // Other body predicates (e.g. equalities) do not occur in
                    // the GCI premises this decomposition handles.
                }
            }
        }

        let y_constraints: Vec<YConstraint> = y_variables
            .iter()
            .map(|y| YConstraint {
                y_concepts: y2concepts.get(y).cloned().unwrap_or_default(),
                x2y_roles: x2y_roles.get(y).cloned().unwrap_or_default(),
                y2x_roles: y2x_roles.get(y).cloned().unwrap_or_default(),
            })
            .collect();

        let z_concepts: Vec<Vec<AtomicConcept>> = z_variables
            .iter()
            .map(|z| z2concepts.get(z).cloned().unwrap_or_default())
            .collect();

        let (consequences_for_blocked_x, consequences_for_nonblocked_x) =
            parse_head(clause, &y_variables, &z_variables);

        DLClauseInfo {
            x_concepts,
            x2x_roles,
            y_variables,
            y_constraints,
            z_variables,
            z_concepts,
            consequences_for_blocked_x,
            consequences_for_nonblocked_x,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Atom, Term};

    fn concept(name: &str) -> AtomicConcept {
        AtomicConcept::create(format!("http://example.org/{name}"))
    }
    fn role(name: &str) -> AtomicRole {
        AtomicRole::create(format!("http://example.org/{name}"))
    }
    fn var(name: &str) -> Term {
        Term::Variable(Variable::create(name))
    }
    fn concept_atom(name: &str, on: &str) -> Atom {
        Atom::create(DLPredicate::AtomicConcept(concept(name)), vec![var(on)])
    }
    fn role_atom(name: &str, from: &str, to: &str) -> Atom {
        Atom::create(DLPredicate::AtomicRole(role(name)), vec![var(from), var(to)])
    }

    #[test]
    fn decomposes_universal_clause() {
        // C(Y1) :- A(X), R(X,Y1)  --  the clausification of A ⊑ ∀R.C.
        let clause = DLClause::create(
            vec![concept_atom("C", "Y1")],
            vec![concept_atom("A", "X"), role_atom("R", "X", "Y1")],
        );
        let info = DLClauseInfo::new(&clause);
        assert_eq!(info.x_concepts, vec![concept("A")]);
        assert!(info.x2x_roles.is_empty());
        assert_eq!(info.y_variables, vec![Variable::create("Y1")]);
        assert_eq!(info.y_constraints.len(), 1);
        assert_eq!(info.y_constraints[0].x2y_roles, vec![role("R")]);
        assert!(info.y_constraints[0].y2x_roles.is_empty());
        assert!(info.y_constraints[0].y_concepts.is_empty());
        assert!(info.z_variables.is_empty());
        // The head C(Y1): blocked checks C on Y1 directly; non-blocked mirrors
        // C onto Y1's blocker.
        assert_eq!(
            info.consequences_for_blocked_x,
            vec![ConsequenceAtom::Simple {
                predicate: DLPredicate::AtomicConcept(concept("C")),
                argument_types: vec![ArgumentType::YVar],
                argument_indexes: vec![0],
            }]
        );
        assert_eq!(
            info.consequences_for_nonblocked_x,
            vec![ConsequenceAtom::MirroredY { concept: concept("C"), y_argument_index: 0 }]
        );
    }

    #[test]
    fn decomposes_role_head_consequences() {
        // S(X,Y1) :- A(X), R(X,Y1)  -- a role-propagation clause.
        let clause = DLClause::create(
            vec![role_atom("S", "X", "Y1")],
            vec![concept_atom("A", "X"), role_atom("R", "X", "Y1")],
        );
        let info = DLClauseInfo::new(&clause);
        // Blocked-X: the X2Y role consequence (real-X adjusted); non-blocked: a
        // plain S(X, Y1) tuple.
        assert_eq!(
            info.consequences_for_blocked_x,
            vec![ConsequenceAtom::X2YOrY2X { role: role("S"), y_argument_index: 0, is_x2y: true }]
        );
        assert_eq!(
            info.consequences_for_nonblocked_x,
            vec![ConsequenceAtom::Simple {
                predicate: DLPredicate::AtomicRole(role("S")),
                argument_types: vec![ArgumentType::XVar, ArgumentType::YVar],
                argument_indexes: vec![0, 0],
            }]
        );
    }

    #[test]
    fn decomposes_inverse_and_z_structure() {
        // B(X) :- A(X), R(Y1,X), D(Y1), E(Z1)  -- inverse link (Y1 → X), a
        // concept on Y1, a self role on X, and a concept-only Z variable.
        let clause = DLClause::create(
            vec![concept_atom("B", "X")],
            vec![
                concept_atom("A", "X"),
                role_atom("S", "X", "X"),
                role_atom("R", "Y1", "X"),
                concept_atom("D", "Y1"),
                concept_atom("E", "Z1"),
            ],
        );
        let info = DLClauseInfo::new(&clause);
        assert_eq!(info.x_concepts, vec![concept("A")]);
        assert_eq!(info.x2x_roles, vec![role("S")]);
        assert_eq!(info.y_variables, vec![Variable::create("Y1")]);
        assert_eq!(info.y_constraints[0].y2x_roles, vec![role("R")]);
        assert!(info.y_constraints[0].x2y_roles.is_empty());
        assert_eq!(info.y_constraints[0].y_concepts, vec![concept("D")]);
        assert_eq!(info.z_variables, vec![Variable::create("Z1")]);
        assert_eq!(info.z_concepts, vec![vec![concept("E")]]);
    }
}
