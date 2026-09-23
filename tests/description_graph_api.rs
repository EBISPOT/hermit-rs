//! Description graphs through the public reasoner API (no issue).
//!
//! OWL syntax cannot express description graphs. HermiT takes them in the
//! `Reasoner(Configuration, OWLOntology, Collection<DescriptionGraph>)`
//! constructor; the port clausified with graphs only crate-internally.
//! `IncrementalReasoner::with_description_graphs` is the public input path,
//! and the graphs must reach every reasoning service, not only consistency.
use hermit_rs::configuration::Configuration;
use hermit_rs::model::{AtomicConcept, AtomicRole, DescriptionGraph, Edge};
use hermit_rs::reasoner::{self, IncrementalReasoner};
use hermit_rs::structural::A;
use horned_owl::model::*;
use horned_owl::ontology::set::SetOntology;

fn ex(name: &str) -> String {
    format!("http://example.org/dg#{name}")
}

/// `G`: vertex 0 `:Car` with a `:hasPart` edge to vertex 1 `:Engine`, started
/// by `:Car`.
fn graph() -> DescriptionGraph {
    let car = AtomicConcept::create(ex("Car"));
    DescriptionGraph::new(
        ex("G"),
        vec![car, AtomicConcept::create(ex("Engine"))],
        vec![Edge::new(AtomicRole::create(ex("hasPart")), 0, 1)],
        [car].into_iter().collect(),
    )
}

/// A rule over the graph property makes anything with an engine part
/// `:Motorised`; only the graph gives a `:Car` such a part.
fn ontology(extra: &str) -> SetOntology<A> {
    let text = format!(
        "Prefix(:=<http://example.org/dg#>)
Ontology(
Declaration(Class(:Car)) Declaration(Class(:Engine)) Declaration(Class(:Motorised))
Declaration(ObjectProperty(:hasPart)) Declaration(NamedIndividual(:herbie))
DLSafeRule(Body(ObjectPropertyAtom(:hasPart Variable(:x) Variable(:y)) ClassAtom(:Engine Variable(:y)))
           Head(ClassAtom(:Motorised Variable(:x))))
ClassAssertion(:Car :herbie)
{extra}
)"
    );
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(text), Default::default())
        .unwrap()
        .0
}

fn with_graph(extra: &str) -> IncrementalReasoner {
    IncrementalReasoner::with_description_graphs(ontology(extra), Configuration::default(), vec![graph()])
}

fn without_graph(extra: &str) -> IncrementalReasoner {
    IncrementalReasoner::with_configuration(ontology(extra), Configuration::default())
}

fn class(name: &str) -> Class<A> {
    Build::new_arc().class(ex(name))
}

fn car_is_motorised() -> Component<A> {
    Component::SubClassOf(SubClassOf {
        sub: ClassExpression::Class(class("Car")),
        sup: ClassExpression::Class(class("Motorised")),
    })
}

#[test]
fn graphs_reach_consistency() {
    let clash = "ClassAssertion(ObjectComplementOf(:Motorised) :herbie)";
    assert!(!with_graph(clash).is_consistent().unwrap());
    assert!(without_graph(clash).is_consistent().unwrap());
    assert!(with_graph("").is_consistent().unwrap());
    assert!(!with_graph("")
        .is_concept_satisfiable(ClassExpression::ObjectIntersectionOf(vec![
            ClassExpression::Class(class("Car")),
            ClassExpression::ObjectComplementOf(Box::new(ClassExpression::Class(class("Motorised")))),
        ]))
        .unwrap());
}

#[test]
fn graphs_reach_classification() {
    let mut reasoner = with_graph("");
    let hierarchy = reasoner.classify().unwrap();
    assert!(hierarchy.super_elements(&class("Car"), false).contains(&class("Motorised")));
    assert!(reasoner.super_classes(&class("Car"), true).unwrap().contains(&class("Motorised")));
    assert!(reasoner.sub_classes(&class("Motorised"), false).unwrap().contains(&class("Car")));
    assert!(reasoner
        .is_subsumed_by(ClassExpression::Class(class("Car")), ClassExpression::Class(class("Motorised")))
        .unwrap());
    assert!(!without_graph("").super_classes(&class("Car"), false).unwrap().contains(&class("Motorised")));
}

#[test]
fn graphs_reach_entailment() {
    assert!(with_graph("").is_entailed(&car_is_motorised()).unwrap());
    assert!(!without_graph("").is_entailed(&car_is_motorised()).unwrap());
}

#[test]
fn graphs_reach_instances() {
    let herbie = Build::new_arc().named_individual(ex("herbie"));
    let mut reasoner = with_graph("");
    assert!(reasoner.instances(&class("Motorised"), false).unwrap().contains(&herbie));
    assert!(reasoner
        .is_instance_of(herbie.clone(), ClassExpression::Class(class("Motorised")))
        .unwrap());
    assert!(!without_graph("").instances(&class("Motorised"), false).unwrap().contains(&herbie));
}

/// The graphs apply to the reasoner's queries only: after a query, the free
/// functions over the same ontology still reason without them.
#[test]
fn graphs_do_not_leak_into_the_free_functions() {
    let mut reasoner = with_graph("");
    assert_eq!(reasoner.description_graphs().len(), 1);
    assert!(reasoner.is_entailed(&car_is_motorised()).unwrap());
    assert!(!reasoner::is_entailed(reasoner.ontology(), &car_is_motorised()).unwrap());
}

/// A change flushed into the reasoner is reasoned over with the graphs too.
#[test]
fn graphs_survive_a_flush() {
    let mut reasoner = with_graph("");
    assert!(reasoner.is_consistent().unwrap());
    let herbie = Build::new_arc().named_individual(ex("herbie"));
    reasoner.add_axiom(Component::ClassAssertion(ClassAssertion {
        ce: ClassExpression::ObjectComplementOf(Box::new(ClassExpression::Class(class("Motorised")))),
        i: Individual::Named(herbie),
    }));
    reasoner.flush();
    assert!(!reasoner.is_consistent().unwrap());
}
