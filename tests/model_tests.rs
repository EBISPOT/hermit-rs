// Tests for the ported foundational layers. The expected values are derived
// directly from the behaviour of the original HermiT Java sources.

use std::collections::HashSet;

use hermit_rs::graph::Graph;
use hermit_rs::model::{
    AtLeastConcept, Atom, AtomicConcept, AtomicRole, Constant, DLClause, DLPredicate, Individual,
    LiteralConcept, Role, Term, Variable,
};
use hermit_rs::prefixes::Prefixes;

#[test]
fn interning_returns_canonical_instances() {
    let a = AtomicConcept::create("http://example.org/A");
    let b = AtomicConcept::create("http://example.org/A");
    let c = AtomicConcept::create("http://example.org/B");
    assert_eq!(a, b);
    // Interning guarantees a single backing allocation -> Java `==` fast path.
    assert!(a.ptr_eq(&b));
    assert_ne!(a, c);
    assert!(!a.ptr_eq(&c));
}

#[test]
fn thing_and_nothing_are_special() {
    let thing = AtomicConcept::thing();
    let nothing = AtomicConcept::nothing();
    assert!(thing.is_always_true());
    assert!(nothing.is_always_false());
    assert!(!thing.is_always_false());

    // getNegation: THING <-> NOTHING, otherwise an AtomicNegationConcept.
    assert_eq!(
        thing.get_negation(),
        LiteralConcept::AtomicConcept(nothing.clone())
    );
    assert_eq!(
        nothing.get_negation(),
        LiteralConcept::AtomicConcept(thing.clone())
    );
    let a = AtomicConcept::create("http://example.org/A");
    match a.get_negation() {
        LiteralConcept::AtomicNegationConcept(neg) => {
            assert_eq!(neg.get_negated_atomic_concept(), &a);
            // Double negation collapses back to the atomic concept.
            assert_eq!(neg.get_negation(), LiteralConcept::AtomicConcept(a.clone()));
        }
        _ => panic!("expected an atomic negation"),
    }
}

#[test]
fn inverse_role_round_trips() {
    let r = AtomicRole::create("http://example.org/r");
    let inv = r.get_inverse();
    match &inv {
        Role::InverseRole(ir) => assert_eq!(ir.get_inverse_of(), &r),
        _ => panic!("expected an inverse role"),
    }
    // Inverse of the inverse is the original role.
    assert_eq!(inv.get_inverse(), Role::AtomicRole(r.clone()));

    // Top/bottom object roles are their own inverses.
    let top = AtomicRole::top_object_role();
    assert_eq!(top.get_inverse(), Role::AtomicRole(top.clone()));
}

#[test]
fn role_assertion_swaps_for_inverse() {
    let r = AtomicRole::create("http://example.org/r");
    let x = Term::Variable(Variable::create("X"));
    let y = Term::Variable(Variable::create("Y"));

    let direct = r.get_role_assertion(x.clone(), y.clone());
    assert_eq!(direct.get_argument(0), &x);
    assert_eq!(direct.get_argument(1), &y);

    let inv = r.get_inverse();
    let inverse_assertion = inv.get_role_assertion(x.clone(), y.clone());
    // inv(r)(X,Y) is stored as r(Y,X).
    assert_eq!(inverse_assertion.get_dl_predicate(), &DLPredicate::AtomicRole(r));
    assert_eq!(inverse_assertion.get_argument(0), &y);
    assert_eq!(inverse_assertion.get_argument(1), &x);
}

#[test]
fn atom_arity_is_checked() {
    let a = AtomicConcept::create("http://example.org/A");
    let x = Term::Variable(Variable::create("X"));
    let atom = Atom::create(DLPredicate::AtomicConcept(a), vec![x.clone()]);
    assert_eq!(atom.get_arity(), 1);
}

#[test]
#[should_panic(expected = "arity")]
fn atom_arity_mismatch_panics() {
    let a = AtomicConcept::create("http://example.org/A");
    let x = Term::Variable(Variable::create("X"));
    let y = Term::Variable(Variable::create("Y"));
    // An atomic concept has arity 1; two arguments must be rejected.
    let _ = Atom::create(DLPredicate::AtomicConcept(a), vec![x, y]);
}

#[test]
fn atomic_concept_inclusion_detection() {
    // A(X) :- B(X) is an atomic concept inclusion.
    let a = AtomicConcept::create("http://example.org/A");
    let b = AtomicConcept::create("http://example.org/B");
    let x = Term::Variable(Variable::create("X"));
    let head = Atom::create(DLPredicate::AtomicConcept(a), vec![x.clone()]);
    let body = Atom::create(DLPredicate::AtomicConcept(b), vec![x]);
    let clause = DLClause::create(vec![head], vec![body]);
    assert!(clause.is_atomic_concept_inclusion());
    // In HermiT a literal concept in the head also makes this a GCI: an atomic
    // concept is a LiteralConcept, so isGeneralConceptInclusion() returns true.
    assert!(clause.is_general_concept_inclusion());
}

#[test]
fn at_least_in_head_is_gci() {
    // atLeast(1 r A)(X) :- B(X) is a general concept inclusion.
    let a = AtomicConcept::create("http://example.org/A");
    let b = AtomicConcept::create("http://example.org/B");
    let r = AtomicRole::create("http://example.org/r");
    let x = Term::Variable(Variable::create("X"));
    let at_least = AtLeastConcept::create(
        1,
        Role::AtomicRole(r),
        LiteralConcept::AtomicConcept(a),
    );
    let head = Atom::create(DLPredicate::AtLeastConcept(at_least), vec![x.clone()]);
    let body = Atom::create(DLPredicate::AtomicConcept(b), vec![x]);
    let clause = DLClause::create(vec![head], vec![body]);
    assert!(clause.is_general_concept_inclusion());
    assert!(!clause.is_atomic_concept_inclusion());
}

#[test]
fn role_inclusion_is_not_gci() {
    // r(X,Y) :- s(X,Y) is an atomic role inclusion, not a GCI.
    let r = AtomicRole::create("http://example.org/r");
    let s = AtomicRole::create("http://example.org/s");
    let x = Term::Variable(Variable::create("X"));
    let y = Term::Variable(Variable::create("Y"));
    let head = Atom::create(DLPredicate::AtomicRole(r), vec![x.clone(), y.clone()]);
    let body = Atom::create(DLPredicate::AtomicRole(s), vec![x, y]);
    let clause = DLClause::create(vec![head], vec![body]);
    assert!(clause.is_atomic_role_inclusion());
    assert!(!clause.is_atomic_role_inverse_inclusion());
    assert!(!clause.is_general_concept_inclusion());
}

#[test]
fn safe_version_adds_atoms_for_unsafe_variables() {
    // A(X) :- (empty body): X is unsafe and must be guarded.
    let a = AtomicConcept::create("http://example.org/A");
    let top = AtomicConcept::thing();
    let x = Term::Variable(Variable::create("X"));
    let head = Atom::create(DLPredicate::AtomicConcept(a), vec![x]);
    let clause = DLClause::create(vec![head], vec![]);
    let safe = clause.get_safe_version(DLPredicate::AtomicConcept(top.clone()));
    assert_eq!(safe.get_body_length(), 1);
    assert_eq!(
        safe.get_body_atom(0).get_dl_predicate(),
        &DLPredicate::AtomicConcept(top.clone())
    );

    // A clause with no unsafe head variables is returned unchanged.
    let b = AtomicConcept::create("http://example.org/B");
    let x2 = Term::Variable(Variable::create("X"));
    let head2 = Atom::create(DLPredicate::AtomicConcept(b.clone()), vec![x2.clone()]);
    let body2 = Atom::create(DLPredicate::AtomicConcept(b), vec![x2]);
    let clause2 = DLClause::create(vec![head2], vec![body2]);
    let safe2 = clause2.get_safe_version(DLPredicate::AtomicConcept(top.clone()));
    assert_eq!(safe2, clause2);
}

#[test]
fn atom_collects_variables_and_individuals() {
    let r = AtomicRole::create("http://example.org/r");
    let x = Variable::create("X");
    let i = Individual::create("http://example.org/i");
    let atom = r.get_role_assertion(Term::Variable(x.clone()), Term::Individual(i.clone()));
    let mut vars = HashSet::new();
    atom.get_variables(&mut vars);
    assert_eq!(vars, HashSet::from([x.clone()]));
    let mut inds = HashSet::new();
    atom.get_individuals(&mut inds);
    assert_eq!(inds, HashSet::from([i]));
    assert!(atom.contains_variable(&x));
}

#[test]
fn constant_enumeration_is_order_independent() {
    let c1 = Constant::create("1", "http://www.w3.org/2001/XMLSchema#integer");
    let c2 = Constant::create("2", "http://www.w3.org/2001/XMLSchema#integer");
    use hermit_rs::model::ConstantEnumeration;
    let e1 = ConstantEnumeration::create(vec![c1.clone(), c2.clone()]);
    let e2 = ConstantEnumeration::create(vec![c2, c1]);
    assert_eq!(e1, e2);
    assert!(e1.ptr_eq(&e2));
}

#[test]
fn to_string_uses_prefixes() {
    let a = AtomicConcept::create("http://www.w3.org/2002/07/owl#Thing");
    // The standard prefixes abbreviate owl#Thing as owl:Thing.
    assert_eq!(a.to_string(), "owl:Thing");

    let unknown = AtomicConcept::create("http://example.org/A");
    assert_eq!(unknown.to_string(), "<http://example.org/A>");
}

#[test]
fn prefixes_abbreviate_and_expand() {
    let std = Prefixes::standard();
    assert_eq!(
        std.abbreviate_iri("http://www.w3.org/2002/07/owl#Thing"),
        "owl:Thing"
    );
    assert_eq!(
        std.expand_abbreviated_iri("owl:Thing").unwrap(),
        "http://www.w3.org/2002/07/owl#Thing"
    );
    assert_eq!(
        std.expand_abbreviated_iri("<http://example.org/x>").unwrap(),
        "http://example.org/x"
    );
}

#[test]
fn dl_ontology_collects_vocabulary_and_horn_flag() {
    use hermit_rs::model::DLOntology;
    use std::collections::{BTreeSet, HashSet};

    // A(X) :- B(X)  and  C(X) v D(X) :- A(X)
    let a = AtomicConcept::create("http://example.org/A");
    let b = AtomicConcept::create("http://example.org/B");
    let c = AtomicConcept::create("http://example.org/C");
    let d = AtomicConcept::create("http://example.org/D");
    let x = || Term::Variable(Variable::create("X"));

    let clause1 = DLClause::create(
        vec![Atom::create(DLPredicate::AtomicConcept(a.clone()), vec![x()])],
        vec![Atom::create(DLPredicate::AtomicConcept(b.clone()), vec![x()])],
    );
    let clause2 = DLClause::create(
        vec![
            Atom::create(DLPredicate::AtomicConcept(c.clone()), vec![x()]),
            Atom::create(DLPredicate::AtomicConcept(d.clone()), vec![x()]),
        ],
        vec![Atom::create(DLPredicate::AtomicConcept(a.clone()), vec![x()])],
    );
    let clauses = indexmap::IndexSet::from([clause1, clause2]);

    // The supplied atomic-concept set (as the clausifier passes the class
    // signature). The external-concept count is taken over this supplied set.
    let supplied: BTreeSet<AtomicConcept> =
        [a.clone(), b.clone(), c.clone(), d.clone()].into_iter().collect();

    let ontology = DLOntology::new(
        "http://example.org/onto",
        clauses,
        HashSet::new(),
        HashSet::new(),
        Some(supplied),
        None,
        None,
        None,
        None,
        None,
        None,
        false,
        false,
        false,
        false,
    );
    // A disjunctive head makes the ontology non-Horn.
    assert!(!ontology.is_horn());
    // All four atomic concepts are collected from the clauses.
    for concept in [&a, &b, &c, &d] {
        assert!(ontology.contains_atomic_concept(concept));
    }
    // All are external (non-internal IRIs).
    assert_eq!(ontology.get_number_of_external_concepts(), 4);
}

#[test]
fn graph_transitive_closure_and_reachability() {
    let mut g: Graph<i32> = Graph::new();
    g.add_edge(1, 2);
    g.add_edge(2, 3);
    g.add_edge(3, 4);
    assert!(g.is_reachable_successor(&1, &4));
    assert!(!g.is_reachable_successor(&4, &1));

    g.transitively_close();
    assert!(g.get_successors(&1).contains(&4));
    assert!(g.get_successors(&1).contains(&3));

    let inv = g.get_inverse();
    assert!(inv.get_successors(&4).contains(&3));
}
