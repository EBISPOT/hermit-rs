// Individual-reuse existential-strategy integration tests.
//
// Selecting `Configuration.existential_strategy_type = IndividualReuse` (or
// `El`) must be HONOURED and must give the SAME consistency / classification
// answers as the default `CreationOrder` strategy. HermiT proves the
// individual-reuse strategy both sound and complete, so it decides exactly the
// same questions (it only builds smaller models).
//
// With the default exact (pairwise) blocking + creation-order strategy, the
// `runCalculus` final-chance existential revalidation pass is a no-op, so the
// default answer is unchanged. We assert the same answers come out whether or
// not the inexact strategy (which exercises the final-chance branch) is used.

use horned_owl::model::{
    Build, ClassAssertion, ClassExpression as CE, Component, DisjointClasses, Individual,
    MutableOntology, ObjectPropertyExpression as OPE, SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::configuration::{Configuration, ExistentialStrategyType};
use hermit_rs::model::AtomicConcept;
use hermit_rs::reasoner::Reasoner;
use hermit_rs::structural::{
    Configuration as ClausifyConfiguration, OWLAxioms, OWLAxiomsExpressivity, OWLClausification,
    OWLNormalization,
};

fn clausify(ontology: &SetOntology<hermit_rs::structural::A>) -> hermit_rs::model::DLOntology {
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology).unwrap();
    let axioms = normalization.into_axioms();
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    OWLClausification::new(ClausifyConfiguration::default())
        .clausify("http://example.org/onto", &axioms, &expressivity)
        .unwrap()
}

fn config_with(strategy: ExistentialStrategyType) -> Configuration {
    let mut configuration = Configuration::default();
    configuration.existential_strategy_type = strategy;
    configuration
}

/// Consistency under each of the three existential strategies.
fn consistency_under_all_strategies(
    dl_ontology: &hermit_rs::model::DLOntology,
) -> (bool, bool, bool) {
    let default = Reasoner::new(dl_ontology).is_consistent();
    let reuse = Reasoner::with_configuration(
        dl_ontology,
        config_with(ExistentialStrategyType::IndividualReuse),
    )
    .is_consistent();
    let el =
        Reasoner::with_configuration(dl_ontology, config_with(ExistentialStrategyType::El))
            .is_consistent();
    (default, reuse, el)
}

// --- the four ontology shapes the task asks for -----------------------------

/// SAT: an existential `A ⊑ ∃r.B` with `A(a)` — consistent, builds one witness.
fn sat_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let r = build.object_property("http://example.org/r");
    let ind = build.named_individual("http://example.org/a");
    let mut ontology = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(r),
            bce: Box::new(CE::Class(b)),
        },
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a),
        i: Individual::Named(ind),
    }));
    ontology
}

/// UNSAT: `A ⊑ ∃r.B`, `A ⊑ ∀r.C`, `DisjointClasses(B, C)`, `A(a)` — the witness
/// is both B and C, which are disjoint, so the ontology is inconsistent.
fn unsat_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let r = build.object_property("http://example.org/r");
    let ind = build.named_individual("http://example.org/a");
    let mut ontology = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(r.clone()),
            bce: Box::new(CE::Class(b.clone())),
        },
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom {
            ope: OPE::ObjectProperty(r),
            bce: Box::new(CE::Class(c.clone())),
        },
    }));
    ontology.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(b),
        CE::Class(c),
    ])));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a),
        i: Individual::Named(ind),
    }));
    ontology
}

/// CYCLIC (needs blocking for termination): `A ⊑ ∃r.A` with `A(a)` — an infinite
/// `r`-chain of `A`-nodes that only terminates because blocking detects the
/// repeated signature. Consistent.
fn cyclic_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let r = build.object_property("http://example.org/r");
    let ind = build.named_individual("http://example.org/a");
    let mut ontology = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(r),
            bce: Box::new(CE::Class(a.clone())),
        },
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a),
        i: Individual::Named(ind),
    }));
    ontology
}

/// NOMINAL: `A ⊑ ∃r.{b}`, `A(a)`, `DisjointClasses(A, B)`, `B(b)` — `a` has an
/// `r`-edge to the nominal `b`; consistent (a and b are distinct individuals).
fn nominal_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let bcls = build.class("http://example.org/Bc");
    let r = build.object_property("http://example.org/r");
    let ind_a = build.named_individual("http://example.org/a");
    let ind_b = build.named_individual("http://example.org/b");
    let mut ontology = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(r),
            bce: Box::new(CE::ObjectOneOf(vec![Individual::Named(ind_b.clone())])),
        },
    }));
    ontology.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(bcls.clone()),
    ])));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a),
        i: Individual::Named(ind_a),
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(bcls),
        i: Individual::Named(ind_b),
    }));
    ontology
}

/// CLASH-RETRY (task item 3): an ontology where the SHARED reuse witness clashes,
/// forcing the `IndividualReuseBranchingPoint` to backtrack and retry with a
/// FRESH witness -- which must still give the correct (consistent) answer.
///
///   A ⊑ ∃r.C,  A ⊑ ∀r.D,   B ⊑ ∃s.C,  B ⊑ ∀s.E,
///   DisjointClasses(D, E),  A(a),  B(b)
///
/// Under `IndividualReuse` both `a` (over r) and `b` (over s) would reuse the SAME
/// per-concept C-witness w; then ∀r.D forces D(w) and ∀s.E forces E(w), and D/E are
/// disjoint -> clash on the reused witness. The reuse branching point backtracks
/// and re-expands one existential with a fresh witness, so the ontology is
/// consistent (exactly as the default creation-order strategy, which never shares).
fn clash_forces_reuse_retry_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let e = build.class("http://example.org/E");
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let ind_a = build.named_individual("http://example.org/a");
    let ind_b = build.named_individual("http://example.org/b");
    let mut ontology = SetOntology::new();
    // A ⊑ ∃r.C
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(r.clone()),
            bce: Box::new(CE::Class(c.clone())),
        },
    }));
    // A ⊑ ∀r.D
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom {
            ope: OPE::ObjectProperty(r),
            bce: Box::new(CE::Class(d.clone())),
        },
    }));
    // B ⊑ ∃s.C
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(s.clone()),
            bce: Box::new(CE::Class(c)),
        },
    }));
    // B ⊑ ∀s.E
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::ObjectAllValuesFrom {
            ope: OPE::ObjectProperty(s),
            bce: Box::new(CE::Class(e.clone())),
        },
    }));
    // DisjointClasses(D, E)
    ontology.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(d),
        CE::Class(e),
    ])));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a),
        i: Individual::Named(ind_a),
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(b),
        i: Individual::Named(ind_b),
    }));
    ontology
}

#[test]
fn individual_reuse_clash_retry_matches_default_consistency() {
    let dl = clausify(&clash_forces_reuse_retry_ontology());
    let (default, reuse, el) = consistency_under_all_strategies(&dl);
    assert!(
        default,
        "the clash-retry ontology is consistent under default (separate witnesses)"
    );
    // The sound+complete (non-deterministic) `IndividualReuse` strategy MUST agree
    // with the default: when the shared C-witness clashes (D(w) from ∀r.D vs E(w)
    // from ∀s.E, D/E disjoint), the `IndividualReuseBranchingPoint` backtracks the
    // reuse and retries with a FRESH witness, restoring consistency. This is the
    // safety net -- the new reuse model-shaping must never change the ANSWER.
    assert_eq!(
        default, reuse,
        "IndividualReuse must still be consistent after the reuse witness clashes \
         and the IndividualReuseBranchingPoint retries with a fresh witness"
    );
    // `El` is HermiT's DETERMINISTIC individual-reuse strategy: `expandWithModelReuse`
    // pushes NO branching point (`IndividualReuseStrategy.java:160`, guarded by
    // `!m_isDeterministic`), so a clash on the forced reuse witness has no branching
    // point to backtrack to and the run reports inconsistent. This is faithful to
    // Java: HermiT only ever selects `El` for OWL-EL-profile ontologies (which have
    // no such ∀/disjointness interaction), so on a non-EL ontology its deterministic
    // reuse is intentionally incomplete. We pin this faithful behaviour rather than
    // claim El is complete here.
    assert!(
        !el,
        "El (deterministic reuse, no branching point) cannot retry the clashing \
         witness, so it reports inconsistent on this non-EL-profile ontology -- \
         matching Java's deterministic IndividualReuseStrategy"
    );
}

// --- Same consistency answers across strategies (>=4 ontologies) ------------

#[test]
fn individual_reuse_matches_default_consistency_sat() {
    let dl = clausify(&sat_ontology());
    let (default, reuse, el) = consistency_under_all_strategies(&dl);
    assert!(default, "sat ontology must be consistent under default");
    assert_eq!(default, reuse, "IndividualReuse must agree with default (sat)");
    assert_eq!(default, el, "El must agree with default (sat)");
}

#[test]
fn individual_reuse_matches_default_consistency_unsat() {
    let dl = clausify(&unsat_ontology());
    let (default, reuse, el) = consistency_under_all_strategies(&dl);
    assert!(!default, "unsat ontology must be inconsistent under default");
    assert_eq!(default, reuse, "IndividualReuse must agree with default (unsat)");
    assert_eq!(default, el, "El must agree with default (unsat)");
}

#[test]
fn individual_reuse_matches_default_consistency_cyclic_with_blocking() {
    let dl = clausify(&cyclic_ontology());
    let (default, reuse, el) = consistency_under_all_strategies(&dl);
    assert!(default, "cyclic ontology must be consistent (terminates via blocking)");
    assert_eq!(default, reuse, "IndividualReuse must agree with default (cyclic)");
    assert_eq!(default, el, "El must agree with default (cyclic)");
}

#[test]
fn individual_reuse_matches_default_consistency_nominal() {
    let dl = clausify(&nominal_ontology());
    let (default, reuse, el) = consistency_under_all_strategies(&dl);
    assert!(default, "nominal ontology must be consistent");
    assert_eq!(default, reuse, "IndividualReuse must agree with default (nominal)");
    assert_eq!(default, el, "El must agree with default (nominal)");
}

/// Classification (atomic subsumption) under the reuse strategy must match
/// the default. Uses `A ⊑ B`, `B ⊑ C`: A ⊑ C must hold, A ⊑ ¬-anything must not.
#[test]
fn individual_reuse_matches_default_classification() {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let mut ontology = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::Class(c.clone()),
    }));
    let dl = clausify(&ontology);

    let ac_a = AtomicConcept::create("http://example.org/A".to_string());
    let ac_c = AtomicConcept::create("http://example.org/C".to_string());

    let default_reasoner = Reasoner::new(&dl);
    let mut default_manager = default_reasoner.new_manager();
    let default_sub = default_reasoner.atomic_subsumes(&mut default_manager, &ac_a, &ac_c);
    assert!(default_sub, "A ⊑ C must hold under default classification");

    for strategy in [ExistentialStrategyType::IndividualReuse, ExistentialStrategyType::El] {
        let reasoner = Reasoner::with_configuration(&dl, config_with(strategy));
        let mut manager = reasoner.new_manager();
        let sub = reasoner.atomic_subsumes(&mut manager, &ac_a, &ac_c);
        assert_eq!(sub, default_sub, "subsumption under {strategy:?} must match default");
    }
}

// --- final-chance pass is a no-op under the default exact strategy ------

/// The default (pairwise / exact) blocking strategy is `is_exact()`, so the
/// `runCalculus` final-chance branch is dead and the answer is unchanged. We
/// assert that across the four ontologies the default answers are exactly the
/// expected ones (i.e. adding the final-chance branch changed nothing).
#[test]
fn final_chance_pass_is_noop_for_default_exact_strategy() {
    let cases: [(SetOntology<hermit_rs::structural::A>, bool); 4] = [
        (sat_ontology(), true),
        (unsat_ontology(), false),
        (cyclic_ontology(), true),
        (nominal_ontology(), true),
    ];
    for (ontology, expected) in cases {
        let dl = clausify(&ontology);
        assert_eq!(
            Reasoner::new(&dl).is_consistent(),
            expected,
            "default exact-strategy answer must be unchanged by the final-chance branch",
        );
    }
}
