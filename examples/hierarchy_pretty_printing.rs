//! Mirrors HermiT's `examples/.../HierarchyPrettyPrinting.java`.
//!
//! The Java example loads `pizza.owl`, builds a `Reasoner`, and writes the
//! inferred class / object-property / data-property hierarchies in OWL
//! functional-style syntax via `printHierarchies` (indented, "pretty") and
//! `dumpHierarchies` (flat set of FSS axioms).
//!
//! This port builds a tiny ontology in code (so the example is self-contained
//! and needs no data files), classifies it, and prints both renderings using
//! the public hierarchy printers:
//!   * `reasoner::print_hierarchies` -> HermiT's `Reasoner.printHierarchies`
//!   * `reasoner::dump_hierarchies`  -> HermiT's `Reasoner.dumpHierarchies`
//!
//! Run with:  cargo run --example hierarchy_pretty_printing

use horned_owl::model::{
    Build, ClassExpression as CE, Component, MutableOntology, SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner;

/// A small "food" taxonomy:  Margherita ⊑ Pizza ⊑ Food, and VegetarianPizza ⊑ Pizza.
fn build_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let food = build.class("http://example.org/food#Food");
    let pizza = build.class("http://example.org/food#Pizza");
    let margherita = build.class("http://example.org/food#Margherita");
    let vegetarian = build.class("http://example.org/food#VegetarianPizza");

    let mut ontology = SetOntology::new();
    let mut sub = |a: &horned_owl::model::Class<hermit_rs::structural::A>,
                   b: &horned_owl::model::Class<hermit_rs::structural::A>| {
        ontology.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(a.clone()),
            sup: CE::Class(b.clone()),
        }));
    };
    sub(&pizza, &food);
    sub(&margherita, &pizza);
    sub(&vegetarian, &pizza);
    ontology
}

fn main() -> Result<(), String> {
    let ontology = build_ontology();

    // HermiT always checks consistency before it will classify.
    println!("Is the ontology consistent? {}", reasoner::is_ontology_consistent(&ontology)?);
    println!();

    // `printHierarchies(out, classes=true, objectProps=true, dataProps=true)`:
    // the indented, "pretty" FSS rendering of the inferred hierarchies.
    println!("=== print_hierarchies (pretty, indented FSS) ===");
    println!("{}", reasoner::print_hierarchies(&ontology, true, true, true)?);
    println!();

    // `dumpHierarchies(out, true, true, true)`: the flat set of FSS axioms.
    println!("=== dump_hierarchies (flat FSS axioms) ===");
    println!("{}", reasoner::dump_hierarchies(&ontology, true, true, true)?);

    Ok(())
}
