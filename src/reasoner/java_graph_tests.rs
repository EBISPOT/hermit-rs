//! Java graph.GraphTest and tableau.GraphTest scenarios.
#![allow(non_snake_case)]
use super::java_tableau_tests::*;
use super::*;
use crate::model::*;
use std::collections::HashSet;
const NS: &str = "file:/c/test.owl#";
fn graph(
    ns: &str,
    vertices: &[&str],
    edges: &[(&str, i32, i32)],
    starts: &[&str],
) -> DescriptionGraph {
    DescriptionGraph::new(
        "G",
        vertices
            .iter()
            .map(|s| AtomicConcept::create(format!("{ns}{s}")))
            .collect(),
        edges
            .iter()
            .map(|(s, a, b)| Edge::new(AtomicRole::create(format!("{ns}{s}")), *a, *b))
            .collect(),
        starts
            .iter()
            .map(|s| AtomicConcept::create(format!("{ns}{s}")))
            .collect(),
    )
}
fn dl_with_graph(axioms: &str, g: DescriptionGraph) -> DLOntology {
    let text = format!(
        "Prefix(:=<{NS}>) Prefix(owl:=<http://www.w3.org/2002/07/owl#>) Ontology({axioms})"
    );
    let (o, _): (
        horned_owl::ontology::set::SetOntology<crate::structural::A>,
        _,
    ) = horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(text), Default::default())
        .unwrap();
    let dl = clausify_ontology(&o).unwrap();
    let mut clauses = dl.get_dl_clauses().clone();
    g.produce_start_dl_clauses(&mut clauses);
    DLOntology::new(
        "opaque:test",
        clauses,
        dl.get_positive_facts().clone(),
        dl.get_negative_facts().clone(),
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        true,
        true,
        true,
        false,
    )
}
fn graph_one(ns: &str) {
    let g = graph(
        ns,
        &["A", "B", "C", "A"],
        &[("R", 0, 1), ("R", 3, 2)],
        &["A"],
    );
    let dl=dl_with_graph("SubClassOf(:A ObjectSomeValuesFrom(:S :A)) SubClassOf(:A ObjectSomeValuesFrom(:S :D)) SubClassOf(:B ObjectSomeValuesFrom(:T :A)) SubClassOf(:C ObjectSomeValuesFrom(:T :A)) FunctionalObjectProperty(:S) ClassAssertion(:A :i)",g);
    let c = crate::configuration::Configuration {
        blocking_strategy_type: crate::configuration::BlockingStrategyType::Anywhere,
        direct_blocking_type: crate::configuration::DirectBlockingType::PairWise,
        ..Default::default()
    };
    assert!(Reasoner::with_configuration(&dl, c).is_consistent());
}
#[test]
fn graph_testGraph1() {
    if crate::java_test_support::isolated("reasoner::java_graph_tests::graph_testGraph1") {
        return;
    }
    graph_one(NS);
}
#[test]
fn tableau_testGraph1() {
    if crate::java_test_support::isolated("reasoner::java_graph_tests::tableau_testGraph1") {
        return;
    }
    graph_one("");
}
#[test]
fn testContradictionOnGraph() {
    if crate::java_test_support::isolated("reasoner::java_graph_tests::testContradictionOnGraph") {
        return;
    }
    let g = graph(NS, &["A", "B"], &[("R", 0, 1)], &["A", "B"]);
    let dl=dl_with_graph("ClassAssertion(:A :a) ClassAssertion(:B :b) DisjointClasses(:A :B) ObjectPropertyAssertion(:r :a :b) DLSafeRule(Body(ObjectPropertyAtom(:R Variable(:x) Variable(:y))) Head(SameIndividualAtom(Variable(:x) Variable(:y))))",g);
    let (mut t, mut manager) = tableau(&dl, false);
    let empty = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let a = t.create_new_named_node(&empty);
    let b = t.create_new_named_node(&empty);
    t.java_add_graph_tuple(g, &[a, b]);
    t.add_role_assertion(
        Role::AtomicRole(AtomicRole::create(format!("{NS}R"))),
        a,
        b,
        &empty,
        true,
    );
    // Java's per-test Individuals are named; install the normal named-node label.
    for n in [a, b] {
        t.add_concept_assertion(
            Concept::AtomicConcept(*AtomicConcept::internal_named()),
            n,
            &empty,
            true,
        );
    }
    assert!(!run_calculus(&mut t, &mut manager).unwrap());
}
#[test]
fn testGraph2() {
    if crate::java_test_support::isolated("reasoner::java_graph_tests::testGraph2") {
        return;
    }
    let g = graph(
        NS,
        &["LP", "RP", "P", "P"],
        &[("S", 0, 1), ("R", 0, 2), ("R", 1, 3)],
        &["P"],
    );
    let dl=dl_with_graph("SubClassOf(:A ObjectSomeValuesFrom(:T :P)) SubClassOf(ObjectSomeValuesFrom(:T :D) :B) DLSafeRule(Body(ClassAtom(:P Variable(:v)) ObjectPropertyAtom(:R Variable(:x) Variable(:v)) ClassAtom(:LP Variable(:x)) ObjectPropertyAtom(:S Variable(:x) Variable(:y)) ClassAtom(:RP Variable(:y)) ObjectPropertyAtom(:R Variable(:y) Variable(:w)) ClassAtom(:P Variable(:w))) Head(ObjectPropertyAtom(:conn Variable(:v) Variable(:w)))) DLSafeRule(Body(ObjectPropertyAtom(:conn Variable(:x) Variable(:y))) Head(ClassAtom(:D Variable(:x)))) DLSafeRule(Body(ObjectPropertyAtom(:conn Variable(:x) Variable(:y))) Head(ClassAtom(:D Variable(:y))))",g);
    let r = Reasoner::new(&dl);
    let mut manager = r.new_manager();
    let individual = Term::Individual(Individual::create("ind"));
    let a = Atom::create(
        DLPredicate::AtomicConcept(AtomicConcept::create(format!("{NS}A"))),
        vec![individual.clone()],
    );
    let b = Atom::create(
        DLPredicate::AtomicConcept(AtomicConcept::create(format!("{NS}B"))),
        vec![individual],
    );
    assert!(!r.is_consistent_with_pos_neg_test_atoms(&mut manager, &[a], &[b]));
}
#[test]
fn testGraphMerging() {
    if crate::java_test_support::isolated("reasoner::java_graph_tests::testGraphMerging") {
        return;
    }
    let g = graph(
        "",
        &["A", "B", "C"],
        &[("R", 0, 1), ("R", 1, 2)],
        &["A", "B", "C"],
    );
    let dl = dl_with_graph("", g);
    let (mut t, mut manager) = tableau(&dl, false);
    let e = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let [n1, n2, n3, n4, n5, n6] = std::array::from_fn(|_| t.create_new_ni_node(&e));
    let r = Concept::AtomicConcept(AtomicConcept::create("R"));
    let s = Concept::AtomicConcept(AtomicConcept::create("S"));
    t.java_add_graph_tuple(g, &[n1, n2, n3]);
    t.java_add_graph_tuple(g, &[n4, n5, n6]);
    t.add_concept_assertion(r, n1, &e, false);
    t.add_concept_assertion(s, n6, &e, false);
    let n7 = t.create_new_ni_node(&e);
    t.java_add_graph_tuple(g, &[n1, n7, n6]);
    for tuple in [[n1, n2, n3], [n4, n5, n6], [n1, n7, n6]] {
        assert!(t.java_contains_graph_tuple(g, &tuple));
    }
    assert!(run_calculus(&mut t, &mut manager).unwrap());
    for (node, expected) in [
        (n1, n1),
        (n2, n7),
        (n3, n6),
        (n4, n1),
        (n5, n7),
        (n6, n6),
        (n7, n7),
    ] {
        assert_eq!(t.get_canonical_node(node), expected);
    }
    for (n, expected) in [(n1, vec![r]), (n5, vec![]), (n6, vec![s])] {
        let actual: HashSet<_> = t
            .atomic_concepts_on_node(n)
            .into_iter()
            .map(Concept::AtomicConcept)
            .collect();
        assert_eq!(actual, expected.into_iter().collect());
    }
    assert!(t.java_contains_graph_tuple(g, &[n1, n7, n6]));
}
