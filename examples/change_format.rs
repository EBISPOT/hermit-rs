//! Closest-supported port of HermiT's `examples/.../ChangeFormat.java`.
//!
//! ## Port-API gap
//! The Java `ChangeFormat` is purely an **OWL-API** demonstration: load an
//! ontology in one syntax and `manager.saveOntology(..., new
//! FunctionalSyntaxDocumentFormat(), ...)` to re-serialise it in another. It
//! exercises NO HermiT reasoning at all -- it is the OWL API's `OWLOntologyManager`
//! format machinery, which the `hermit_rs` crate does not re-export and is not a
//! reasoning service.
//!
//! The `hermit_rs` crate is built on `horned-owl`, which DOES provide the OWL
//! functional-style-syntax writer (`horned_owl::io::ofn`) and the `AsFunctional`
//! rendering trait. This example therefore does the closest supported thing:
//! it builds an ontology and re-serialises it to functional-style syntax using
//! horned-owl's writer -- mirroring `ChangeFormat`'s "save as FSS" step. Parsing
//! `.ofn` / `.owx` files in the other direction is what the crate's CLI loader
//! (`hermit_rs::cli::load_ontology`) does.
//!
//! Run with:  cargo run --example change_format

use horned_owl::io::ofn::writer::AsFunctional;
use horned_owl::model::{
    Build, ClassExpression as CE, Component, MutableOntology, ObjectPropertyExpression as OPE,
    SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

fn build_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let pizza = build.class("http://example.org/pizza#Pizza");
    let food = build.class("http://example.org/pizza#Food");
    let has_topping = build.object_property("http://example.org/pizza#hasTopping");
    let topping = build.class("http://example.org/pizza#Topping");

    let mut ontology = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(pizza.clone()),
        sup: CE::Class(food),
    }));
    // Pizza ⊑ ∃hasTopping.Topping
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(pizza),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(has_topping),
            bce: Box::new(CE::Class(topping)),
        },
    }));
    ontology
}

fn main() {
    let ontology = build_ontology();

    // Re-serialise every component to OWL functional-style syntax -- the same
    // target format `ChangeFormat` writes with FunctionalSyntaxDocumentFormat.
    println!("Ontology(");
    let mut lines: Vec<String> = ontology
        .iter()
        .map(|ac| format!("  {}", ac.component.as_functional()))
        .collect();
    lines.sort();
    for line in lines {
        println!("{line}");
    }
    println!(")");
}
