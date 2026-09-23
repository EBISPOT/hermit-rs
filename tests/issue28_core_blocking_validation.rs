//! Issues #28, #29 and #30: under core blocking the three Widmann ontologies,
//! which have no model, were reported consistent.
//!
//! Core blocking (`SIMPLE_CORE`/`COMPLEX_CORE`, HermiT's
//! `AnywhereValidatedBlocking`) blocks a node on its core label alone, which is
//! not sound by itself: once nothing else is left to do, the final-chance pass
//! validates the blocks against the full labels, unblocks the nodes whose blocks
//! are invalid, and expansion continues from them. The existential expansion
//! resumes its node walk at a cursor that it advances past blocked nodes,
//! relying on every blocking pass to pull the cursor back to a node that it
//! leaves unblocked with existentials still to expand. The anywhere and ancestor
//! passes did; the validated passes did not. So the nodes that validation
//! unblocked were never expanded, and the tableau was taken for a model although
//! their existentials were unsatisfied.
//!
//! Expanding them exposed two defects that Rust shares with HermiT, which a
//! comparison of every blocking configuration on random ontologies found:
//!
//! * The validation checks the parent of a blocked node once per pass and
//!   records that on the parent, but it cleared the record only from the first
//!   node that it validated. A parent before that node kept the record, and the
//!   next pass accepted a block that violates the parent's constraints, so two
//!   more inconsistent ontologies were reported consistent (below).
//! * After a validation, pre-blocking blocks a node again only once the node or
//!   a candidate blocker has changed, but it revisited only the nodes from the
//!   first change of a core label. A node that was invalidly blocked was never
//!   reconsidered, and the derivation below it need not end (below).
//!
//! Every blocking strategy decides the same question, so each configuration must
//! agree with the unsatisfiability arguments given beside each ontology. A
//! satisfiable variant of each Widmann ontology, one axiom weaker, must stay
//! consistent.
use hermit_rs::{configuration::*, reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;
use std::time::{Duration, Instant};

fn parse(axioms: &str) -> SetOntology<A> {
    let source = format!(
        r#"Prefix(:=<urn:issue28:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(
{axioms}
)"#
    );
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
        .unwrap()
        .0
}

fn configuration(
    blocking: BlockingStrategyType,
    direct: DirectBlockingType,
    existential: ExistentialStrategyType,
) -> Configuration {
    Configuration {
        blocking_strategy_type: blocking,
        direct_blocking_type: direct,
        blocking_signature_cache_type: BlockingSignatureCacheType::NotCached,
        existential_strategy_type: existential,
        ..Configuration::default()
    }
}

/// The default configuration, both core-blocking strategies with every direct
/// blocking checker and existential strategy, and the exact anywhere strategy,
/// with the exact ancestor strategy too when `ancestor` is set. Ancestor
/// blocking lets the model of the satisfiable variant of Widmann3 grow for
/// longer than a test should run, in HermiT as in Rust, so it only checks the
/// inconsistent ontologies.
fn configurations(ancestor: bool) -> Vec<(String, Configuration)> {
    use BlockingStrategyType::*;
    use DirectBlockingType::*;
    use ExistentialStrategyType::*;
    let mut result = vec![("the default configuration".to_string(), Configuration::default())];
    for blocking in [SimpleCore, ComplexCore] {
        for direct in [Single, PairWise, DirectBlockingType::Optimal] {
            for existential in [CreationOrder, IndividualReuse] {
                result.push((
                    format!("{blocking:?}/{direct:?}/{existential:?}"),
                    configuration(blocking, direct, existential),
                ));
            }
        }
    }
    let exact: &[BlockingStrategyType] = if ancestor { &[Anywhere, Ancestor] } else { &[Anywhere] };
    for &blocking in exact {
        for direct in [Single, PairWise] {
            result.push((
                format!("{blocking:?}/{direct:?}"),
                configuration(blocking, direct, CreationOrder),
            ));
        }
    }
    result
}

fn assert_consistency(axioms: &str, expected: bool) {
    let ontology = parse(axioms);
    for (label, configuration) in configurations(!expected) {
        assert_eq!(
            reasoner::is_ontology_consistent_with_configuration(&ontology, &configuration)
                .unwrap(),
            expected,
            "consistency under {label} of\n{axioms}"
        );
    }
}

/// `testWidmann1` (#28). Every element `x` has an `a`-successor, which has an
/// `a`-successor `z`. The universal restriction on `z` leads back from `z` to `x`
/// along `a⁻` twice, then along `b` to any `b`-successor `y` of `x` and along
/// `b⁻` back to `x`, so `p(x)` whenever `x` has a `b`-successor. The last axiom
/// gives every element a `b`-successor, so every element is a `p`; but that
/// `b`-successor is an `∀a.∃a.¬p`, and it has an `a`-successor, which then has an
/// `a`-successor outside `p`.
const WIDMANN1: &str = "InverseObjectProperties(:a :a-)
InverseObjectProperties(:b :b-)
SubClassOf(owl:Thing ObjectAllValuesFrom(:a- ObjectAllValuesFrom(:a- ObjectAllValuesFrom(:b ObjectAllValuesFrom(:b- :p)))))
SubClassOf(owl:Thing ObjectSomeValuesFrom(:a :p))";

/// `testWidmann2` (#29), the ABox version that the core-blocking suite
/// substitutes. Every element `x` has an `r`-predecessor `y` in
/// `∀r⁻.∀r.∀r.∀r.p`, and `y` has an `r`-predecessor `w`. Then `w` is in
/// `∀r.∀r.∀r.p`, `y` in `∀r.∀r.p` and `x` in `∀r.p`: every `r`-successor of an
/// element is a `p`. The `r`-predecessor of `:a` outside `p` has an
/// `r`-predecessor, whose `r`-successor it is.
const WIDMANN2: &str = "InverseObjectProperties(:r :r-)
SubClassOf(owl:Thing ObjectSomeValuesFrom(:r- ObjectAllValuesFrom(:r- ObjectAllValuesFrom(:r ObjectAllValuesFrom(:r ObjectAllValuesFrom(:r :p))))))
SubClassOf(owl:Thing ObjectSomeValuesFrom(:r :q))";

/// `testWidmann3` (#30). Let `y` be an `r`-successor of some `x`. The first
/// axiom gives `y` an `r`-successor `z` in `∀r⁻.∃r.∀r⁻.∀r.p`, so `y`, an
/// `r`-predecessor of `z`, has an `r`-successor in `∀r⁻.∀r.p`, whose
/// `r`-predecessor `y` is then an `∀r.p`. The second and third axioms give every
/// element an `r`-predecessor, so every element is an `∀r.p` and, as the
/// `r`-successor of its `r`-predecessor, a `p`. The last axiom gives some element
/// an `r`-successor `v` in `∀r.∃r⁻.¬p`; `v` has an `r`-successor by the first
/// axiom, which has an `r`-predecessor outside `p`.
const WIDMANN3: &str = "InverseObjectProperties(:r :r-)
SubClassOf(owl:Thing ObjectAllValuesFrom(:r ObjectSomeValuesFrom(:r ObjectAllValuesFrom(:r- ObjectSomeValuesFrom(:r ObjectAllValuesFrom(:r- ObjectAllValuesFrom(:r :p)))))))
SubClassOf(owl:Thing ObjectSomeValuesFrom(:r- ObjectAllValuesFrom(:r- ObjectSomeValuesFrom(:r- ObjectSomeValuesFrom(:r- ObjectAllValuesFrom(:r ObjectAllValuesFrom(:r :p)))))))
SubClassOf(owl:Thing ObjectSomeValuesFrom(:r- ObjectSomeValuesFrom(:r :p)))";

#[test]
fn widmann1_is_inconsistent_under_every_blocking_strategy() {
    assert_consistency(
        &format!(
            "{WIDMANN1}
SubClassOf(owl:Thing ObjectSomeValuesFrom(:b ObjectAllValuesFrom(:a ObjectSomeValuesFrom(:a ObjectComplementOf(:p)))))"
        ),
        false,
    );
}

#[test]
fn widmann1_without_the_complement_is_consistent() {
    assert_consistency(
        &format!(
            "{WIDMANN1}
SubClassOf(owl:Thing ObjectSomeValuesFrom(:b ObjectAllValuesFrom(:a ObjectSomeValuesFrom(:a :p))))"
        ),
        true,
    );
}

#[test]
fn widmann2_is_inconsistent_under_every_blocking_strategy() {
    assert_consistency(
        &format!(
            "{WIDMANN2}
ClassAssertion(ObjectSomeValuesFrom(:r- ObjectComplementOf(:p)) :a)"
        ),
        false,
    );
}

#[test]
fn widmann2_without_the_complement_is_consistent() {
    assert_consistency(
        &format!(
            "{WIDMANN2}
ClassAssertion(ObjectSomeValuesFrom(:r- :p) :a)"
        ),
        true,
    );
}

#[test]
fn widmann3_is_inconsistent_under_every_blocking_strategy() {
    assert_consistency(
        &format!(
            "{WIDMANN3}
SubClassOf(owl:Thing ObjectSomeValuesFrom(:r- ObjectSomeValuesFrom(:r ObjectAllValuesFrom(:r ObjectSomeValuesFrom(:r- ObjectComplementOf(:p))))))"
        ),
        false,
    );
}

#[test]
fn widmann3_without_the_complement_is_consistent() {
    assert_consistency(
        &format!(
            "{WIDMANN3}
SubClassOf(owl:Thing ObjectSomeValuesFrom(:r- ObjectSomeValuesFrom(:r ObjectAllValuesFrom(:r ObjectSomeValuesFrom(:r- :p)))))"
        ),
        true,
    );
}

/// By the third axiom every element has an `r0`-successor in
/// `∀r0⁻.∃r1.∀r1.¬C`, so every element has an `r1`-successor in `∀r1.¬C`, and an
/// `r0`-successor in `∀r0.C`, whose own `r0`-successor `y` is a `C`. By the
/// second axiom the `r1`-successor `z` of `y` in `∀r1.¬C` is a `C`, as is the
/// `r1`-successor that the first axiom gives `z`, which `∀r1.¬C` excludes. The
/// single-checker core configurations accepted a block that violates `∀r0.C` of
/// the blocked node's parent, because an earlier pass had checked that parent.
#[test]
fn every_validation_checks_the_parents_again() {
    assert_consistency(
        "SubClassOf(owl:Thing ObjectSomeValuesFrom(:r1 ObjectAllValuesFrom(ObjectInverseOf(:r0) ObjectSomeValuesFrom(:r1 ObjectComplementOf(:C)))))
SubClassOf(ObjectSomeValuesFrom(ObjectInverseOf(:r1) :C) :C)
SubClassOf(owl:Thing ObjectSomeValuesFrom(:r0 ObjectIntersectionOf(ObjectAllValuesFrom(ObjectInverseOf(:r0) ObjectSomeValuesFrom(:r1 ObjectAllValuesFrom(:r1 ObjectComplementOf(:C)))) ObjectAllValuesFrom(:r0 :C))))",
        false,
    );
}

/// By the second axiom every element has an `r0`-successor in
/// `∀r0⁻.∀r1.¬C0`, so every element is an `∀r1.¬C0`. By the first, every
/// element, as an `r0`-predecessor, has an `r1`-predecessor in `∀r0.C0`, so
/// every element is outside `C0`, but the `r0`-successor of that
/// `r1`-predecessor is a `C0`. HermiT's single-checker simple core
/// configuration reports this ontology consistent too; clearing the record of
/// the checked parents corrects it there as well.
#[test]
fn every_validation_checks_the_parents_again_unlike_hermit() {
    assert_consistency(
        "SubClassOf(owl:Thing ObjectAllValuesFrom(ObjectInverseOf(:r0) ObjectIntersectionOf(ObjectSomeValuesFrom(ObjectInverseOf(:r1) :C2) ObjectSomeValuesFrom(ObjectInverseOf(:r1) ObjectAllValuesFrom(:r0 :C0)))))
SubClassOf(owl:Thing ObjectSomeValuesFrom(:r0 ObjectAllValuesFrom(ObjectInverseOf(:r0) ObjectAllValuesFrom(:r1 ObjectComplementOf(:C0)))))
SubClassOf(ObjectAllValuesFrom(:r0 ObjectComplementOf(:C2)) :C2)
SubClassOf(:C2 ObjectSomeValuesFrom(ObjectInverseOf(:r1) :C1))",
        false,
    );
}

/// Runs `check` against a deadline, since the defect it guards against is a
/// derivation that never ends.
fn within_deadline(check: impl FnOnce() + Send + 'static) {
    let handle = std::thread::spawn(check);
    let deadline = Instant::now() + Duration::from_secs(60);
    while !handle.is_finished() {
        assert!(Instant::now() < deadline, "the derivation does not end");
        std::thread::sleep(Duration::from_millis(10));
    }
    if let Err(panic) = handle.join() {
        std::panic::resume_unwind(panic);
    }
}

/// Every element has an `r`-predecessor, created as its tree successor, and its
/// `r`-successors' `r`-successors' `r`-successors are `A`s. So a node gets its
/// full label only from three generations of descendants, and a leaf, whose
/// parent lacks what the blocker's copy would require, has no valid blocker.
/// Pre-blocking has to block a node again once its label has grown; HermiT's
/// core blocking, like Rust's before, never ends on this ontology.
#[test]
fn core_blocking_reconsiders_a_node_whose_label_grows() {
    within_deadline(|| {
        assert_consistency(
            "SubClassOf(owl:Thing ObjectSomeValuesFrom(ObjectInverseOf(:r) :B))
SubClassOf(owl:Thing ObjectAllValuesFrom(:r ObjectAllValuesFrom(:r ObjectAllValuesFrom(:r :A))))",
            true,
        )
    });
}
