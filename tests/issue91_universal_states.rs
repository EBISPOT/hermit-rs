//! Domain and range axioms on a complex role hold a state of the role's
//! automaton at every node: the initial state of `⊤ ⊑ ∀R.C`, the final states
//! of `∃R.⊤ ⊑ D` (`∀R.⊥`). Those states are eliminated from the clauses
//! (EBISPOT/hermit-rs#91), so the entailments they encode must survive: along
//! a single edge, along a transitive chain, along a property chain, at the
//! class level and at the instance level, and nothing must become universal.

use hermit_rs::reasoner::{is_concept_satisfiable, is_entailed, is_subsumed_by};
use horned_owl::model::{
    Build, ClassAssertion, ClassExpression as CE, Component, Individual, ObjectPropertyExpression as OPE,
};
use horned_owl::ontology::set::SetOntology;

type Onto = SetOntology<hermit_rs::structural::A>;

fn parse(text: &str) -> Onto {
    let (onto, _): (
        horned_owl::ontology::component_mapped::ComponentMappedOntology<
            hermit_rs::structural::A,
            horned_owl::model::AnnotatedComponent<hermit_rs::structural::A>,
        >,
        _,
    ) = horned_owl::io::ofn::reader::read(
        &mut std::io::Cursor::new(text),
        horned_owl::io::ParserConfiguration::new(Build::new_arc()),
    )
    .expect("parse");
    onto.into()
}

/// `R` is transitive with the chain `P ∘ R ⊑ R` and the chain `R ∘ Q ⊑ R`, so
/// its automaton has more than one accepting state; `R` has range `C` and
/// domain `D`. The ABox is `P(d, a)`, `R(a, b)`, `R(b, c)`, `Q(c, e)`.
fn ontology(extra: &str) -> Onto {
    parse(&format!(
        "Prefix(:=<http://example.org/>)\n\
         Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
         Ontology(<http://example.org/universal-states>\n\
         Declaration(ObjectProperty(:R)) Declaration(ObjectProperty(:P))\n\
         Declaration(ObjectProperty(:Q))\n\
         Declaration(Class(:C)) Declaration(Class(:D)) Declaration(Class(:E))\n\
         Declaration(Class(:F)) Declaration(Class(:G))\n\
         Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
         Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:d))\n\
         Declaration(NamedIndividual(:e))\n\
         TransitiveObjectProperty(:R)\n\
         SubObjectPropertyOf(ObjectPropertyChain(:P :R) :R)\n\
         SubObjectPropertyOf(ObjectPropertyChain(:R :Q) :R)\n\
         ObjectPropertyRange(:R :C)\n\
         ObjectPropertyDomain(:R :D)\n\
         ObjectPropertyAssertion(:P :d :a)\n\
         ObjectPropertyAssertion(:R :a :b)\n\
         ObjectPropertyAssertion(:R :b :c)\n\
         ObjectPropertyAssertion(:Q :c :e)\n\
         {extra}\
         )\n"
    ))
}

fn class(name: &str) -> CE<hermit_rs::structural::A> {
    CE::Class(Build::new_arc().class(format!("http://example.org/{name}")))
}

fn role(name: &str) -> OPE<hermit_rs::structural::A> {
    OPE::ObjectProperty(Build::new_arc().object_property(format!("http://example.org/{name}")))
}

fn some(name: &str, filler: CE<hermit_rs::structural::A>) -> CE<hermit_rs::structural::A> {
    CE::ObjectSomeValuesFrom { ope: role(name), bce: Box::new(filler) }
}

fn thing() -> CE<hermit_rs::structural::A> {
    CE::Class(Build::new_arc().class("http://www.w3.org/2002/07/owl#Thing"))
}

fn has_type(onto: &Onto, individual: &str, name: &str) -> bool {
    let build = Build::new_arc();
    is_entailed(
        onto,
        &Component::ClassAssertion(ClassAssertion {
            ce: class(name),
            i: Individual::Named(build.named_individual(format!("http://example.org/{individual}"))),
        }),
    )
    .expect("entailment")
}

#[test]
fn range_and_domain_reach_every_individual_the_role_connects() {
    let onto = ontology("");
    // Sources of an R edge, of the transitive closure and of the chains.
    for source in ["a", "b", "d"] {
        assert!(has_type(&onto, source, "D"), "{source} is in the domain");
    }
    // Targets likewise: c through transitivity, e through R ∘ Q ⊑ R.
    for target in ["b", "c", "e"] {
        assert!(has_type(&onto, target, "C"), "{target} is in the range");
    }
    // Nothing beyond the edges: d has no incoming R edge and e no outgoing one.
    assert!(!has_type(&onto, "d", "C"));
    assert!(!has_type(&onto, "e", "D"));
    assert!(!has_type(&onto, "a", "C"));
}

#[test]
fn range_and_domain_hold_at_the_class_level_but_are_not_universal() {
    let onto = ontology("SubClassOf(:E ObjectSomeValuesFrom(:P ObjectSomeValuesFrom(:R :F)))\n");
    assert!(is_subsumed_by(&onto, some("R", thing()), class("D")).unwrap());
    assert!(is_subsumed_by(&onto, some("P", some("R", thing())), class("D")).unwrap());
    assert!(is_subsumed_by(&onto, class("E"), class("D")).unwrap());
    assert!(is_subsumed_by(&onto, some("R", some("Q", thing())), some("R", class("C"))).unwrap());
    // The states were universal; the classes are not.
    assert!(!is_subsumed_by(&onto, thing(), class("C")).unwrap());
    assert!(!is_subsumed_by(&onto, thing(), class("D")).unwrap());
    assert!(!is_subsumed_by(&onto, class("E"), class("C")).unwrap());
}

#[test]
fn a_class_with_no_successors_over_the_role_is_still_closed() {
    // `∀R.⊥` outside a domain axiom: the same universal final states.
    let onto = ontology("SubClassOf(:G ObjectAllValuesFrom(:R owl:Nothing))\n");
    assert!(is_concept_satisfiable(&onto, class("G")).unwrap());
    let g_with = |successor: CE<hermit_rs::structural::A>| {
        CE::ObjectIntersectionOf(vec![class("G"), successor])
    };
    assert!(!is_concept_satisfiable(&onto, g_with(some("R", thing()))).unwrap());
    assert!(!is_concept_satisfiable(&onto, g_with(some("P", some("R", thing())))).unwrap());
    assert!(is_concept_satisfiable(&onto, g_with(some("Q", thing()))).unwrap());
}
