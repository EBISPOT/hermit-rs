//! Mirrors HermiT's `examples/.../Explanations.java`.
//!
//! The Java example uses the OWL API's `BlackBoxExplanation` +
//! `HSTExplanationGenerator` (Reiter's hitting-set tree over a single-justification
//! black-box oracle) to enumerate ALL justifications for (a) the unsatisfiability
//! of a class and (b) the inconsistency of the whole ontology. It also flips
//! `Configuration.throwInconsistentOntologyException = false` so the inconsistent
//! case can be explained rather than throwing.
//!
//! The port ships exactly this service natively:
//!   * `reasoner::explain`           -> a single (minimal) justification (black-box shrink)
//!   * `reasoner::all_explanations`  -> ALL justifications via Reiter's hitting-set tree
//!     (the direct equivalent of `HSTExplanationGenerator.getExplanations`)
//!
//! A class C being unsatisfiable is the entailment `SubClassOf(C, owl:Nothing)`,
//! so we justify that axiom -- the same thing `BlackBoxExplanation` explains for
//! an unsatisfiable class.
//!
//! Run with:  cargo run --example explanations

use horned_owl::model::{
    Build, ClassExpression as CE, Component, DisjointClasses, MutableOntology, SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner;

/// IceCream is forced unsatisfiable:
///   IceCream ⊑ CheeseTopping,  IceCream ⊑ VegetableTopping,
///   DisjointClasses(CheeseTopping, VegetableTopping)
/// plus an unrelated axiom that must NOT appear in the justification.
fn build_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let icecream = build.class("http://example.org/pizza#IceCream");
    let cheese = build.class("http://example.org/pizza#CheeseTopping");
    let veg = build.class("http://example.org/pizza#VegetableTopping");
    let pizza = build.class("http://example.org/pizza#Pizza");
    let food = build.class("http://example.org/pizza#Food");

    let mut ontology = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(icecream.clone()),
        sup: CE::Class(cheese.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(icecream),
        sup: CE::Class(veg.clone()),
    }));
    ontology.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(cheese),
        CE::Class(veg),
    ])));
    // Unrelated -- it should not be part of any justification for IceCream ⊑ ⊥.
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(pizza),
        sup: CE::Class(food),
    }));
    ontology
}

fn render(axiom: &Component<hermit_rs::structural::A>) -> String {
    fn name(ce: &CE<hermit_rs::structural::A>) -> String {
        match ce {
            CE::Class(c) => {
                let s = c.0.to_string();
                s.rsplit(['#', '/']).next().unwrap_or(&s).to_string()
            }
            other => format!("{other:?}"),
        }
    }
    match axiom {
        Component::SubClassOf(ax) => format!("SubClassOf( {} {} )", name(&ax.sub), name(&ax.sup)),
        Component::DisjointClasses(ax) => format!(
            "DisjointClasses( {} )",
            ax.0.iter().map(name).collect::<Vec<_>>().join(" ")
        ),
        other => format!("{other:?}"),
    }
}

fn main() -> Result<(), String> {
    let ontology = build_ontology();
    let build = Build::new_arc();
    let icecream = build.class("http://example.org/pizza#IceCream");
    let nothing = build.class("http://www.w3.org/2002/07/owl#Nothing");

    // Confirm IceCream is unsatisfiable (Java: reasoner.isSatisfiable(icecream)).
    let satisfiable =
        reasoner::is_concept_satisfiable(&ontology, CE::Class(icecream.clone()))?;
    println!("Is IceCream satisfiable? {satisfiable}");
    println!("Computing explanations for IceCream ⊑ owl:Nothing ...");
    println!();

    // The unsatisfiability is the entailment SubClassOf(IceCream, owl:Nothing).
    let goal = Component::SubClassOf(SubClassOf {
        sub: CE::Class(icecream),
        sup: CE::Class(nothing),
    });

    // ALL justifications -- the direct equivalent of HSTExplanationGenerator.
    let explanations = reasoner::all_explanations(&ontology, &goal)?;
    for (i, explanation) in explanations.iter().enumerate() {
        println!("------------------");
        println!("Explanation {} -- axioms causing the unsatisfiability:", i + 1);
        let mut lines: Vec<String> = explanation.iter().map(render).collect();
        lines.sort();
        for line in lines {
            println!("  {line}");
        }
        println!("------------------");
    }

    // A single minimal justification (BlackBoxExplanation's oracle).
    if let Some(one) = reasoner::explain(&ontology, &goal)? {
        println!();
        println!("A single minimal justification has {} axiom(s).", one.len());
    }

    Ok(())
}
