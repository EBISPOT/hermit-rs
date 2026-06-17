// Integration tests for the blocking-strategy / direct-blocking / signature-cache
// selection (`Reasoner.createTableau`): the configuration selects the blocking
// strategy (Anywhere / Ancestor / validated core), the direct-blocking checker
// (Single / Pairwise), and the optional BlockingSignatureCache.
//
// Every HermiT blocking strategy is sound AND complete, so a non-default
// selection decides the SAME sat / unsat / classification questions as the
// default -- they differ only in model shape / termination depth. These tests
// therefore assert that each selectable value gives the CORRECT (and identical)
// answer on sat / unsat / cyclic-with-blocking (A ⊑ ∃r.A) / nominal /
// inverse-role ontologies, plus a default-config-unchanged check.

use horned_owl::model::{
    Build, ClassAssertion, ClassExpression as CE, Component, DisjointClasses, Individual,
    InverseObjectProperties, MutableOntology, ObjectPropertyExpression as OPE, SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::configuration::{
    BlockingSignatureCacheType, BlockingStrategyType, Configuration, DirectBlockingType,
};
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

// --- the selectable blocking configurations -----------------------------------

fn blocking_config(
    strategy: BlockingStrategyType,
    direct: DirectBlockingType,
    cache: BlockingSignatureCacheType,
) -> Configuration {
    let mut configuration = Configuration::default();
    configuration.blocking_strategy_type = strategy;
    configuration.direct_blocking_type = direct;
    configuration.blocking_signature_cache_type = cache;
    configuration
}

/// Every distinct blocking configuration the dispatch can produce. Each is a
/// `(label, Configuration)` so a failure pinpoints the strategy.
fn all_blocking_configs() -> Vec<(&'static str, Configuration)> {
    use BlockingSignatureCacheType::{Cached, NotCached};
    use BlockingStrategyType::{Ancestor, Anywhere, ComplexCore, Optimal, SimpleCore};
    use DirectBlockingType::{Optimal as DOptimal, PairWise, Single};
    vec![
        ("default(optimal/optimal/cached)", blocking_config(Optimal, DOptimal, Cached)),
        ("anywhere/single/cached", blocking_config(Anywhere, Single, Cached)),
        ("anywhere/pairwise/cached", blocking_config(Anywhere, PairWise, Cached)),
        ("anywhere/single/not_cached", blocking_config(Anywhere, Single, NotCached)),
        ("anywhere/pairwise/not_cached", blocking_config(Anywhere, PairWise, NotCached)),
        ("ancestor/single/cached", blocking_config(Ancestor, Single, Cached)),
        ("ancestor/pairwise/cached", blocking_config(Ancestor, PairWise, Cached)),
        ("ancestor/optimal/not_cached", blocking_config(Ancestor, DOptimal, NotCached)),
        ("simple_core/optimal/cached", blocking_config(SimpleCore, DOptimal, Cached)),
        ("complex_core/optimal/cached", blocking_config(ComplexCore, DOptimal, Cached)),
        ("simple_core/single/cached", blocking_config(SimpleCore, Single, Cached)),
    ]
}

/// Run `is_consistent` under every blocking configuration and assert it equals
/// `expected` for each (the strategies all decide the same question).
fn assert_consistency_under_all_configs(
    dl_ontology: &hermit_rs::model::DLOntology,
    expected: bool,
    shape: &str,
) {
    // The default reasoner first, as the reference.
    let reference = Reasoner::new(dl_ontology).is_consistent();
    assert_eq!(reference, expected, "default reasoner on {shape}");
    for (label, configuration) in all_blocking_configs() {
        let result =
            Reasoner::with_configuration(dl_ontology, configuration).is_consistent();
        assert_eq!(
            result, expected,
            "blocking config `{label}` must decide {shape} == {expected}"
        );
    }
}

// --- the ontology shapes ------------------------------------------------------

/// SAT: `A ⊑ ∃r.B`, `A(a)` — consistent.
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

/// UNSAT: `A ⊑ ∃r.B`, `A ⊑ ∀r.C`, `DisjointClasses(B,C)`, `A(a)` — inconsistent.
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

/// CYCLIC (needs blocking for termination): `A ⊑ ∃r.A`, `A(a)` — an infinite
/// `r`-chain that only terminates because blocking detects the repeated
/// signature. Consistent. This is the central test that the OTHER strategies
/// (single/ancestor/core/cache) also terminate AND agree.
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

/// NOMINAL: `A ⊑ ∃r.{b}`, `DisjointClasses(A,Bc)`, `A(a)`, `Bc(b)` — consistent.
/// With nominals the dispatch builds NO signature cache (Java's `!hasNominals`
/// guard), so this exercises the cache-disabling arm too.
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

/// INVERSE-ROLE (cyclic + backward propagation): `A ⊑ ∃r.A`, `A ⊑ ∀Inv(r).C`,
/// `InverseObjectProperties(r, ri)`, `A(a)` — the classic case where SINGLE
/// blocking is incomplete, so the dispatch must pick PAIRWISE (OPTIMAL) here.
/// Consistent. This is the ontology that distinguishes single from pairwise.
fn inverse_role_ontology() -> SetOntology<hermit_rs::structural::A> {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let r = build.object_property("http://example.org/r");
    let ri = build.object_property("http://example.org/ri");
    let ind = build.named_individual("http://example.org/a");
    let mut ontology = SetOntology::new();
    // A ⊑ ∃r.A
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(r.clone()),
            bce: Box::new(CE::Class(a.clone())),
        },
    }));
    // A ⊑ ∀Inv(r).C  (written over ri with ri ≡ Inv(r))
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom {
            ope: OPE::InverseObjectProperty(r.clone()),
            bce: Box::new(CE::Class(c)),
        },
    }));
    ontology.insert(Component::InverseObjectProperties(InverseObjectProperties(
        OPE::ObjectProperty(r), OPE::ObjectProperty(ri),
    )));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a),
        i: Individual::Named(ind),
    }));
    ontology
}

// --- the tests ----------------------------------------------------------------

#[test]
fn every_blocking_strategy_decides_sat() {
    let dl = clausify(&sat_ontology());
    assert_consistency_under_all_configs(&dl, true, "SAT (A ⊑ ∃r.B)");
}

#[test]
fn every_blocking_strategy_decides_unsat() {
    let dl = clausify(&unsat_ontology());
    assert_consistency_under_all_configs(&dl, false, "UNSAT (∃r.B ⊓ ∀r.C, B⊓C⊑⊥)");
}

#[test]
fn every_blocking_strategy_terminates_and_agrees_on_the_cyclic_ontology() {
    // The defining test: A ⊑ ∃r.A only terminates via blocking. Single, pairwise,
    // ancestor, the validated core strategies and the signature cache must all
    // terminate AND report consistent.
    let dl = clausify(&cyclic_ontology());
    assert_consistency_under_all_configs(&dl, true, "CYCLIC (A ⊑ ∃r.A)");
}

#[test]
fn every_blocking_strategy_decides_the_nominal_ontology() {
    let dl = clausify(&nominal_ontology());
    assert_consistency_under_all_configs(&dl, true, "NOMINAL (A ⊑ ∃r.{b})");
}

#[test]
fn every_blocking_strategy_decides_the_inverse_role_ontology() {
    // With inverse roles single blocking is incomplete; OPTIMAL picks pairwise,
    // and the explicit pairwise / core / ancestor configs must all stay
    // sound+complete and report consistent (with termination).
    let dl = clausify(&inverse_role_ontology());
    assert_consistency_under_all_configs(&dl, true, "INVERSE (A ⊑ ∃r.A, A ⊑ ∀Inv(r).C)");
}

#[test]
fn default_config_is_unchanged() {
    // The DEFAULT configuration must give the SAME answer as the explicit default
    // reasoner on every shape -- the regression guard the task requires.
    for (shape, ontology, expected) in [
        ("sat", sat_ontology(), true),
        ("unsat", unsat_ontology(), false),
        ("cyclic", cyclic_ontology(), true),
        ("nominal", nominal_ontology(), true),
        ("inverse", inverse_role_ontology(), true),
    ] {
        let dl = clausify(&ontology);
        let default = Reasoner::new(&dl).is_consistent();
        let explicit = Reasoner::with_configuration(&dl, Configuration::default()).is_consistent();
        assert_eq!(default, explicit, "default vs explicit-default on {shape}");
        assert_eq!(default, expected, "default config answer on {shape}");
    }
}

#[test]
fn signature_cache_is_reused_across_tests_on_one_reasoner() {
    // a reasoner built with the (default) CACHED config populates its
    // signature cache from a found model. Running multiple consistency checks on
    // the same reasoner over the cyclic ontology must keep giving the correct
    // answer (the cache short-circuit must not change soundness).
    let dl = clausify(&cyclic_ontology());
    let reasoner = Reasoner::with_configuration(
        &dl,
        blocking_config(
            BlockingStrategyType::Anywhere,
            DirectBlockingType::Single,
            BlockingSignatureCacheType::Cached,
        ),
    );
    // Each call builds a fresh per-test tableau but shares the reasoner config;
    // the answer must be stable and correct.
    for _ in 0..3 {
        assert!(reasoner.is_consistent(), "cached single anywhere stays consistent");
    }
}
