//! Mirrors HermiT's `examples/.../HermiTConfigurations.java`.
//!
//! The Java example builds a `Configuration`, sets a non-default
//! `tableauMonitorType` (TIMING) and runs a satisfiability test, then builds a
//! second `Configuration` with a `CountingMonitor`, classifies, and reads off
//! the number of tests / timings / model size from the monitor.
//!
//! This port mirrors both halves with the public API:
//!   * `Reasoner::with_configuration` -> HermiT's `new Reasoner(config, ontology)`
//!   * `configuration::Configuration` fields (e.g. `existential_strategy_type`,
//!     `blocking_strategy_type`) -> HermiT's `Configuration` fields
//!   * `Reasoner::is_consistent_with_monitor` + `monitor::CountingMonitor`
//!     -> HermiT's `config.monitor = new CountingMonitor()` then reading the
//!        counters off the monitor after reasoning.
//!
//! Because `Reasoner::with_configuration` consumes a clausified `DLOntology`, we
//! run the same front-end clausification pipeline the CLI uses (normalize ->
//! clausify) -- all of which is public on `hermit_rs::structural`.
//!
//! Run with:  cargo run --example hermit_configurations

use horned_owl::model::{
    Build, ClassExpression as CE, Component, MutableOntology, ObjectPropertyExpression as OPE,
    SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::configuration::{Configuration, ExistentialStrategyType};
use hermit_rs::model::DLOntology;
use hermit_rs::monitor::CountingMonitor;
use hermit_rs::reasoner::Reasoner;
use hermit_rs::structural::{
    BuiltInPropertyManager, Configuration as ClausifyConfiguration, ObjectPropertyInclusionManager,
    OWLAxioms, OWLAxiomsExpressivity, OWLClausification, OWLNormalization,
};

/// The CLI's front-end pipeline, made local so this example is self-contained.
/// (`reasoner::clausify_*` is private; the building blocks it uses are public.)
fn clausify(ontology: &SetOntology<hermit_rs::structural::A>) -> Result<DLOntology, String> {
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology)?;
    let definitions_count = normalization.definitions_count();
    let mut axioms = normalization.into_axioms();
    BuiltInPropertyManager::new().axiomatize_built_in_properties_as_needed(&mut axioms);
    if !axioms.complex_object_property_inclusions.is_empty() {
        let manager = ObjectPropertyInclusionManager::new(&mut axioms)?;
        manager.rewrite_negative_object_property_assertions(&mut axioms, definitions_count);
        manager.rewrite_axioms(&mut axioms, 0)?;
    }
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    OWLClausification::new(ClausifyConfiguration::default()).clausify(
        "http://example.org/config-demo",
        &axioms,
        &expressivity,
    )
}

/// An ontology with an existential so the tableau actually builds a model:
///   A ⊑ ∃r.B,  B ⊑ C
fn build_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let a = build.class("http://example.org/c#A");
    let b = build.class("http://example.org/c#B");
    let c = build.class("http://example.org/c#C");
    let r = build.object_property("http://example.org/c#r");
    let mut ontology = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(r),
            bce: Box::new(CE::Class(b.clone())),
        },
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b),
        sup: CE::Class(c),
    }));
    ontology
}

fn main() -> Result<(), String> {
    let ontology = build_ontology();
    let dl_ontology = clausify(&ontology)?;

    // --- Part 1: a NON-default configuration ---------------------------------
    // The Java example sets `config.tableauMonitorType = TIMING`. The port's
    // built-in timing/debugger monitors are internal; the user-visible knobs are
    // the strategy/blocking fields. We pick a non-default existential strategy to
    // show that `with_configuration` actually threads the choice into the tableau
    // (HermiT proves IndividualReuse sound+complete, so the ANSWER is unchanged).
    let mut config = Configuration::default();
    config.existential_strategy_type = ExistentialStrategyType::IndividualReuse;
    let reasoner = Reasoner::with_configuration(&dl_ontology, config);
    println!(
        "Is the ABox satisfiable (IndividualReuse strategy)? {}",
        reasoner.is_consistent()
    );
    println!("--------------------------");

    // --- Part 2: a CountingMonitor (HermiT's config.monitor) -----------------
    // Mirrors `config.monitor = new CountingMonitor()` then reading the counters
    // off the monitor after a reasoning task.
    let reasoner = Reasoner::new(&dl_ontology);
    let (consistent, monitor): (bool, CountingMonitor) =
        reasoner.is_consistent_with_monitor(CountingMonitor::new());

    println!("Consistency result: {consistent}");
    println!("HermiT did {} tests.", monitor.overall_number_of_tests());
    println!("This took {} ms.", monitor.overall_time());
    println!("The last test took {} ms.", monitor.time());
    println!(
        "The last model contained {} live nodes/individuals.",
        monitor.number_of_live_nodes()
    );

    Ok(())
}
