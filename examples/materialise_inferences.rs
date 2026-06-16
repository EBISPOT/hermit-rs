//! Mirrors HermiT's `examples/.../MaterialiseInferences.java`.
//!
//! The Java example uses HermiT as an `OWLReasoner` together with the OWL API's
//! `InferredOntologyGenerator` / `InferredSubClassAxiomGenerator` /
//! `InferredClassAssertionAxiomGenerator` / `InferredDisjointClassesAxiomGenerator`
//! to materialise the inferred subclass, class-assertion and disjoint-class
//! axioms into a new ontology.
//!
//! The port has no OWL-API `InferredAxiomGenerator` machinery, but it exposes
//! the underlying reasoning services those generators call. This example
//! materialises the same three inference kinds directly:
//!   * inferred (direct) subclass axioms  -> `reasoner::sub_classes(.., direct=true)`
//!   * inferred class assertions          -> `reasoner::realize` (the ABox realisation,
//!                                            i.e. each individual's direct types) and
//!                                            `reasoner::instances`
//!   * inferred disjoint classes          -> `reasoner::disjoint_classes`
//!
//! Run with:  cargo run --example materialise_inferences

use horned_owl::model::{
    Build, ClassAssertion, ClassExpression as CE, Component, DisjointClasses, Individual,
    MutableOntology, SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner;

type Class = horned_owl::model::Class<hermit_rs::structural::A>;

/// Animals taxonomy with two disjoint leaves and one asserted individual:
///   Cat ⊑ Pet ⊑ Animal,  Dog ⊑ Pet,  DisjointClasses(Cat, Dog),  Cat(felix)
fn build_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let animal = build.class("http://example.org/zoo#Animal");
    let pet = build.class("http://example.org/zoo#Pet");
    let cat = build.class("http://example.org/zoo#Cat");
    let dog = build.class("http://example.org/zoo#Dog");
    let felix = build.named_individual("http://example.org/zoo#felix");

    let mut ontology = SetOntology::new();
    for (a, b) in [(&pet, &animal), (&cat, &pet), (&dog, &pet)] {
        ontology.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(a.clone()),
            sup: CE::Class(b.clone()),
        }));
    }
    ontology.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(cat.clone()),
        CE::Class(dog.clone()),
    ])));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(cat),
        i: Individual::Named(felix),
    }));
    ontology
}

fn short(c: &Class) -> String {
    c.0.to_string().rsplit(['#', '/']).next().unwrap_or("").to_string()
}

fn main() -> Result<(), String> {
    let ontology = build_ontology();
    let build = Build::new_arc();

    println!("Is the ontology consistent? {}", reasoner::is_ontology_consistent(&ontology)?);
    println!();

    // --- Inferred (direct) SubClassOf axioms (InferredSubClassAxiomGenerator) ---
    println!("=== materialised SubClassOf axioms (direct) ===");
    let hierarchy = reasoner::classify(&ontology)?;
    let mut classes: Vec<Class> = hierarchy.all_elements().cloned().collect();
    classes.sort_by_key(|c| c.0.to_string());
    for class in &classes {
        for sup in reasoner::super_classes(&ontology, class, true)? {
            println!("SubClassOf( {} {} )", short(class), short(&sup));
        }
    }
    println!();

    // --- Inferred class assertions (InferredClassAssertionAxiomGenerator) ---
    // `realize` maps each named individual to its DIRECT types.
    println!("=== materialised ClassAssertion axioms (direct types) ===");
    let realisation = reasoner::realize(&ontology)?;
    let mut individuals: Vec<_> = realisation.keys().cloned().collect();
    individuals.sort_by_key(|i| i.0.to_string());
    for individual in &individuals {
        for ty in &realisation[individual] {
            let name = individual.0.to_string();
            let name = name.rsplit(['#', '/']).next().unwrap_or("");
            println!("ClassAssertion( {} {} )", short(ty), name);
        }
    }
    println!();

    // `instances` is the dual: every (here, non-direct) instance of a class.
    let pet = build.class("http://example.org/zoo#Pet");
    let pet_instances = reasoner::instances(&ontology, &pet, false)?;
    println!(
        "All instances of Pet (inferred): {}",
        pet_instances.len()
    );
    println!();

    // --- Inferred disjoint classes (InferredDisjointClassesAxiomGenerator) ---
    println!("=== materialised DisjointClasses axioms ===");
    let cat = build.class("http://example.org/zoo#Cat");
    let mut disjoint: Vec<Class> = reasoner::disjoint_classes(&ontology, &cat)?.into_iter().collect();
    disjoint.sort_by_key(|c| c.0.to_string());
    for other in disjoint {
        println!("DisjointClasses( {} {} )", short(&cat), short(&other));
    }

    Ok(())
}
