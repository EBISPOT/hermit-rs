//! A DL-safe rule binds named individuals only. The fresh individual every
//! concept test asserts its concept on is anonymous, so a rule never fires on
//! it: `A(?x) -> B(?x)` makes the named `:a` a `:B` without making `:A` a
//! subclass of `:B`, and `C(?x) -> owl:Nothing(?x)` leaves `:C` satisfiable.
//! Each classification route is asked: the classified hierarchy, the
//! subsumption test, and the satisfiability test.
use hermit_rs::{reasoner, structural::A};
use horned_owl::{model::*, ontology::set::SetOntology};
use std::collections::HashSet;

const THING: &str = "http://www.w3.org/2002/07/owl#Thing";

fn ontology() -> SetOntology<A> {
    let source = r#"Prefix(:=<urn:rules:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(
Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
Declaration(NamedIndividual(:a))
ClassAssertion(:A :a)
DLSafeRule(Body(ClassAtom(:A Variable(<urn:rules:x>))) Head(ClassAtom(:B Variable(<urn:rules:x>))))
DLSafeRule(Body(ClassAtom(:C Variable(<urn:rules:x>))) Head(ClassAtom(owl:Nothing Variable(<urn:rules:x>))))
)"#;
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
        .unwrap()
        .0
}

fn class(name: &str) -> Class<A> {
    Build::new_arc().class(format!("urn:rules:{name}"))
}

#[test]
fn a_rule_subsumes_no_class() {
    let o = ontology();
    let thing: HashSet<Class<A>> = [Build::new_arc().class(THING)].into_iter().collect();
    assert_eq!(reasoner::super_classes(&o, &class("A"), false).unwrap(), thing);
    assert_eq!(reasoner::super_classes(&o, &class("C"), false).unwrap(), thing);
    assert!(!reasoner::is_subsumed_by(
        &o,
        ClassExpression::Class(class("A")),
        ClassExpression::Class(class("B")),
    )
    .unwrap());
    assert!(reasoner::is_concept_satisfiable(&o, ClassExpression::Class(class("C"))).unwrap());
}

#[test]
fn a_rule_types_a_named_individual() {
    let o = ontology();
    let a = Build::new_arc().named_individual("urn:rules:a");
    let types = reasoner::get_types(&o, &a, true).unwrap();
    let expected: HashSet<Class<A>> = [class("A"), class("B")].into_iter().collect();
    assert_eq!(types, expected);
}
