//! Mirrors HermiT's `examples/.../EntailmentChecking.java`.
//!
//! The Java example loads `pizza.owl`, then asks (via HermiT's native
//! `Reasoner.isEntailed`) whether
//!     SubClassOf(Margherita, ObjectSomeValuesFrom(hasTopping,
//!                            ObjectUnionOf(MozzarellaTopping, GoatsCheeseTopping)))
//! is entailed, and afterwards lists the (named) subclasses of the complex
//! superclass with `getSubClasses`.
//!
//! This port mirrors the structure with a small self-contained ontology and the
//! public entailment API:
//!   * `reasoner::is_entailed`        -> HermiT's `Reasoner.isEntailed(OWLAxiom)`
//!   * `reasoner::is_entailed_axioms` -> HermiT's `Reasoner.isEntailed(Set<OWLAxiom>)`
//!   * `reasoner::sub_classes`        -> HermiT's `Reasoner.getSubClasses`
//!
//! Run with:  cargo run --example entailment_checking

use horned_owl::model::{
    Build, ClassExpression as CE, Component, MutableOntology, ObjectPropertyExpression as OPE,
    SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner;

/// Margherita ⊑ ∃hasTopping.MozzarellaTopping, MozzarellaTopping ⊑ CheeseTopping.
fn build_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let margherita = build.class("http://example.org/pizza#Margherita");
    let mozzarella = build.class("http://example.org/pizza#MozzarellaTopping");
    let cheese = build.class("http://example.org/pizza#CheeseTopping");
    let has_topping = build.object_property("http://example.org/pizza#hasTopping");

    let mut ontology = SetOntology::new();
    // Margherita ⊑ ∃hasTopping.MozzarellaTopping
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(margherita),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(has_topping),
            bce: Box::new(CE::Class(mozzarella.clone())),
        },
    }));
    // MozzarellaTopping ⊑ CheeseTopping
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(mozzarella),
        sup: CE::Class(cheese),
    }));
    ontology
}

fn main() -> Result<(), String> {
    let ontology = build_ontology();
    let build = Build::new_arc();

    let margherita = build.class("http://example.org/pizza#Margherita");
    let mozzarella = build.class("http://example.org/pizza#MozzarellaTopping");
    let cheese = build.class("http://example.org/pizza#CheeseTopping");
    let has_topping = build.object_property("http://example.org/pizza#hasTopping");

    // The complex superclass:  ∃hasTopping.(MozzarellaTopping ⊔ CheeseTopping)
    let complex = CE::ObjectSomeValuesFrom {
        ope: OPE::ObjectProperty(has_topping),
        bce: Box::new(CE::ObjectUnionOf(vec![
            CE::Class(mozzarella),
            CE::Class(cheese.clone()),
        ])),
    };

    // The axiom to test:  SubClassOf(Margherita, complex)
    let axiom = Component::SubClassOf(SubClassOf {
        sub: CE::Class(margherita),
        sup: complex,
    });

    println!(
        "Do margherita pizzas have a topping that is mozzarella or cheese? {}",
        reasoner::is_entailed(&ontology, &axiom)?
    );

    // The same query through the set-entailment entry point.
    println!(
        "  (via is_entailed_axioms): {}",
        reasoner::is_entailed_axioms(&ontology, std::slice::from_ref(&axiom))?
    );

    // A NON-entailed axiom, to show the negative case:
    //   SubClassOf(Margherita, CheeseTopping)  is NOT entailed.
    let non_entailed = Component::SubClassOf(SubClassOf {
        sub: CE::Class(build.class("http://example.org/pizza#Margherita")),
        sup: CE::Class(cheese.clone()),
    });
    println!(
        "Is every Margherita itself a CheeseTopping? {}",
        reasoner::is_entailed(&ontology, &non_entailed)?
    );
    println!();

    // Like the Java example: list the named subclasses of CheeseTopping.
    println!("Subclasses of CheeseTopping (indirect included):");
    let mut subs: Vec<_> = reasoner::sub_classes(&ontology, &cheese, false)?.into_iter().collect();
    subs.sort_by_key(|c| c.0.to_string());
    for sub in subs {
        let name = sub.0.to_string();
        println!("  {}", name.rsplit(['#', '/']).next().unwrap_or(&name));
    }

    Ok(())
}
