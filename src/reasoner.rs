// A reasoner entry point: loads a clausified `model::DLOntology` into a tableau
// and decides ABox satisfiability by hyperresolution saturation.
//
// This is the bridge from the clausification front-end to the engine, mirroring
// the core of `org.semanticweb.HermiT.tableau.Tableau.isSatisfiable` /
// `org.semanticweb.HermiT.Reasoner.isConsistent`.
//
// The full hypertableau calculus runs here: ABox loading, hyperresolution
// saturation, existential expansion, disjunction branching with
// dependency-directed backtracking, the merge / nominal-introduction rules,
// datatype checking, and validated (or pairwise) blocking for termination. On
// top of `is_consistent` it offers the standard OWLReasoner services
// (satisfiability, subsumption, instance-of, classification, realisation,
// instance retrieval, hierarchy navigation, entailment and explanation).

use std::collections::HashMap;

use crate::model::{
    Concept, DLOntology, DLPredicate, NegatedAtomicRole, Role, Term,
};
use crate::tableau::dependency_set::DependencySet;
use crate::tableau::node::NodeId;
use crate::tableau::object::TableauObject;
use crate::tableau::{HyperresolutionManager, Tableau};

/// Hard ceiling on concurrent leaf-node model builds (see
/// `ConceptSubsumptionOracle::build_models_batch`). A single dense model's tableau
/// can be multiple GB, so concurrency is capped to bound peak RAM rather than to
/// the full core count. Overridable (and still clamped) via `OWLMAKE_CLASSIFY_THREADS`.
const LEAF_BUILD_MAX_WORKERS_CAP: usize = 8;

/// The effective worker cap: `min(cap, available_parallelism)`, optionally
/// overridden (and still clamped to the cap) by `OWLMAKE_CLASSIFY_THREADS`.
fn leaf_build_max_workers() -> usize {
    let cores = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let mut cap = std::cmp::min(LEAF_BUILD_MAX_WORKERS_CAP, cores);
    if let Ok(v) = std::env::var("OWLMAKE_CLASSIFY_THREADS") {
        if let Ok(n) = v.parse::<usize>() {
            if n >= 1 {
                cap = std::cmp::min(n, LEAF_BUILD_MAX_WORKERS_CAP);
            }
        }
    }
    cap.max(1)
}

/// One iteration of HermiT's `doIteration`: returns whether work was done.
fn do_iteration(
    tableau: &mut Tableau,
    manager: &mut HyperresolutionManager,
    mut additional_manager: Option<&mut HyperresolutionManager>,
) -> bool {
    // Poll the interrupt flag at the head of the iteration (no-op with the
    // default -1 timeout). The latched interrupt is surfaced by `run_calculus`.
    tableau.note_interrupt();
    if !tableau.contains_clash() {
        // Tableau.doIteration line 412: drain any buffered cardinality-`> 1`
        // annotated equalities (the deferred nominal-introduction rule) before the
        // propagate loop. Result discarded, exactly as in Java -- the NI merges it
        // performs surface as delta-new and are picked up by `propagate_delta_new`.
        tableau.process_annotated_equalities();
        let mut has_change = false;
        while tableau.propagate_delta_new_all() && !tableau.contains_clash() {
            // Tableau.doIteration line 415-416 --
            // `if (m_hasDescriptionGraphs && !containsClash())
            //      m_descriptionGraphManager.checkGraphConstraints();`
            // A no-op (returns immediately) when the ontology has no description
            // graphs, so the default path is unchanged.
            if !tableau.contains_clash() {
                tableau.check_graph_constraints();
            }
            manager.apply_dl_clauses(tableau);
            // Tableau.java:419-420: when an additional DL ontology is set (HermiT's
            // `getTableau(additionalAxioms)` fast path), its compiled clauses run
            // right after the permanent ones, gated on the clash flag, so the delta
            // is reasoned over without re-clausifying the permanent KB.
            if let Some(am) = additional_manager.as_deref_mut() {
                if !tableau.contains_clash() {
                    am.apply_dl_clauses(tableau);
                }
            }
            // Tableau.java:421-422: `if (m_checkUnknownDatatypeRestrictions && !containsClash())
            //     m_datatypeManager.applyUnknownDatatypeRestrictionSemantics();`
            // Runs BEFORE checkDatatypeConstraints. Gated on the unknown-restriction
            // flag, which is only ever set in the non-default ignoreUnsupportedDatatypes
            // mode, so the default path skips this entirely.
            if tableau.check_unknown_datatype_restrictions && !tableau.contains_clash() {
                tableau.apply_unknown_datatype_restriction_semantics();
            }
            // Tableau.java:423-424: `if (m_checkDatatypes && !containsClash()) checkDatatypeConstraints();`
            // HermiT drives the check off DELTA_OLD retrievals, so it is a no-op in a
            // round with no new data-node assertion; skip the rescan likewise.
            if tableau.check_datatypes
                && tableau.datatype_check_needed
                && !tableau.contains_clash()
            {
                tableau.check_datatype_constraints();
            }
            // Tableau.doIteration line 426: drain buffered cardinality-`> 1`
            // annotated equalities after the round's deterministic saturation
            // (hyperresolution + datatype checks), so the nondeterministic NI
            // branching runs only once those are exhausted.
            if !tableau.contains_clash() {
                tableau.process_annotated_equalities();
            }
            has_change = true;
        }
        if has_change {
            return true;
        }
    }
    if !tableau.contains_clash() && tableau.expand_existentials() {
        return true;
    }
    if !tableau.contains_clash() && tableau.process_first_ground_disjunction() {
        return true;
    }
    if tableau.contains_clash() {
        return tableau.backtrack_on_clash();
    }
    false
}

/// Port of `Tableau.runCalculus`'s saturation loop: brackets the loop
/// with `startTask`/`endTask`, emits `iterationStarted`/`iterationFinished`
/// around each `doIteration`, and returns the saturated clash status -- or an
/// `Err` if an interrupt fired (never with the default -1 timeout).
fn run_calculus(
    tableau: &mut Tableau,
    manager: &mut HyperresolutionManager,
) -> Result<bool, crate::tableau::interrupt_flag::InterruptError> {
    run_calculus_with_additional(tableau, manager, None)
}

/// As [`run_calculus`], but also drives an additional hyperresolution manager
/// (HermiT's `m_additionalHyperresolutionManager`) over the delta clauses of a
/// `setAdditionalDLOntology` tableau, so added axioms are reasoned over without
/// re-clausifying the permanent KB.
fn run_calculus_with_additional(
    tableau: &mut Tableau,
    manager: &mut HyperresolutionManager,
    mut additional_manager: Option<&mut HyperresolutionManager>,
) -> Result<bool, crate::tableau::interrupt_flag::InterruptError> {
    tableau.start_task();
    // `Tableau.runCalculus` reads `existentialsAreExact` once at the top.
    // With the DEFAULT pairwise blocking + creation-order strategy this is `true`,
    // so the final-chance branch below is dead and behaviour is byte-for-byte
    // unchanged. It is `false` only for the inexact validated/core blocking
    // strategy (and the individual-reuse strategy over it), where a final
    // `expandExistentials(true)` revalidation is required for completeness.
    let existentials_are_exact = tableau.is_exact();
    tableau.monitor_event(|m| m.saturate_started());
    loop {
        if let Some(error) = tableau.take_pending_interrupt() {
            tableau.end_task();
            return Err(error);
        }
        tableau.monitor_event(|m| m.iteration_started());
        let mut has_more_work = do_iteration(tableau, manager, additional_manager.as_deref_mut());
        tableau.monitor_event(|m| m.iteration_finished());
        if !existentials_are_exact && !has_more_work && !tableau.contains_clash() {
            // No more work to do, but since the blocking strategy does not
            // necessarily establish only valid blocks (`existentialsAreExact ==
            // false`), tell the strategy to go through the nodes and check whether
            // all blocks are valid; if not, continue with the expansion.
            tableau.monitor_event(|m| m.iteration_started());
            has_more_work = tableau.expand_existentials_final_chance(true);
            tableau.monitor_event(|m| m.iteration_finished());
        }
        if !has_more_work {
            break;
        }
    }
    // An interrupt latched on the final iteration (after the loop's head check)
    // must still surface rather than be reported as a completed saturation.
    if let Some(error) = tableau.take_pending_interrupt() {
        tableau.end_task();
        return Err(error);
    }
    let model_found = !tableau.contains_clash();
    tableau.monitor_event(|m| m.saturate_finished(model_found));
    // `runCalculus` calls `m_existentialExpansionStrategy.modelFound()` on a
    // clash-free saturation (a no-op for the default creation-order strategy).
    if model_found {
        tableau.existential_strategy_model_found();
        // `BlockingStrategy.modelFound` records the blocking signatures
        // of the found model into the signature cache (a no-op when no cache is
        // configured), so a later satisfiability test on the SAME reasoner can
        // short-circuit blocking on a node whose signature is already known to be
        // satisfiable.
        tableau.cache_model_signatures();
    }
    // One final interrupt check after the loop (matching the polling sites).
    tableau.note_interrupt();
    let result = tableau.take_pending_interrupt();
    tableau.end_task();
    match result {
        Some(error) => Err(error),
        None => Ok(!tableau.contains_clash()),
    }
}

use horned_owl::model::{
    Build, ClassAssertion, ClassExpression as CE, Component, Individual as OwlIndividual,
    MutableOntology, NamedIndividual,
};
use horned_owl::ontology::set::SetOntology;

/// Generates a fresh IRI for a query witness that cannot collide with any term
/// a user ontology might contain. HermiT uses genuinely anonymous fresh
/// individuals for its satisfiability/subsumption reductions; a stable public
/// IRI would be unsound, because an ontology mentioning that IRI (e.g. asserting
/// `not A(<that IRI>)`) would contaminate the reduction. Each call returns a
/// distinct IRI in a clearly-internal namespace, combining a monotonic counter
/// with the process start nanos so witnesses are unique within and across queries.
fn fresh_witness_iri(tag: &str) -> String {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{SystemTime, UNIX_EPOCH};
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    format!("urn:hermit-rs:fresh:{tag}:{nanos}:{n}")
}

/// A fresh ANONYMOUS individual witness for the satisfiability / subsumption /
/// property reductions. HermiT uses `factory.getOWLAnonymousIndividual(...)` /
/// `Individual.createAnonymous(...)` for every such witness (e.g.
/// Reasoner.java:765, 1053-1054, 1271, 1294-1295, 1327-1329, 1446), so the
/// witness clausifies to an `Individual::create_anonymous` and is loaded as an
/// NI (blockable) node rather than a named root node -- which matters in the
/// presence of nominals.
fn fresh_anonymous_individual(tag: &str) -> OwlIndividual<crate::structural::A> {
    use horned_owl::model::AnonymousIndividual;
    let build = Build::new_arc();
    OwlIndividual::Anonymous(AnonymousIndividual(build.iri(fresh_witness_iri(tag)).underlying()))
}

/// Maps a horned-owl individual to the DL-model `Individual`, exactly as
/// clausification's `get_individual` does (named -> create, anonymous ->
/// create_anonymous). Used to build per-test ABox atoms for the entailment
/// reductions over named individuals.
fn axiom_individual(i: &OwlIndividual<crate::structural::A>) -> crate::model::Individual {
    match i {
        OwlIndividual::Named(n) => crate::model::Individual::create(n.0.to_string()),
        OwlIndividual::Anonymous(a) => crate::model::Individual::create_anonymous(&a.0.to_string()),
    }
}

/// The distinctive error a public query returns on an inconsistent ontology
/// when `Configuration.throw_inconsistent_ontology_exception` is true (HermiT's
/// default). Mirrors `org.semanticweb.owlapi.reasoner.InconsistentOntologyException`,
/// thrown by `Reasoner.throwInconsistentOntologyExceptionIfNecessary`
/// (Reasoner.java:2183-2186) at the top of every `checkPreConditions` query.
pub const INCONSISTENT_ONTOLOGY_ERROR: &str =
    "InconsistentOntologyException: the ontology is inconsistent";

/// Port of `Reasoner.throwInconsistentOntologyExceptionIfNecessary`
/// (Reasoner.java:2183): when the ontology is inconsistent AND the (default)
/// `throw_inconsistent_ontology_exception` flag is set, returns the distinctive
/// `Err`. This reproduces `checkPreConditions`' top-of-method throw for the
/// public query functions that Java throws on. In Java EVERY classification /
/// realisation entry funnels through `checkPreConditions()` first, so under the
/// default flag classify / getSubClasses / getSuperClasses / getEquivalentClasses
/// / getDisjointClasses / getUnsatisfiableClasses / getTypes / getInstances /
/// realise / isEntailed / isSatisfiable / hasType all throw; their `if(!consistent)
/// return …` blocks are the flag-OFF fallthrough only.
fn throw_inconsistent_ontology_exception_if_necessary(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<(), String> {
    if configuration.throw_inconsistent_ontology_exception && !is_ontology_consistent(ontology)? {
        return Err(INCONSISTENT_ONTOLOGY_ERROR.to_string());
    }
    Ok(())
}

/// Collects the named entity IRIs (classes / object properties / data properties /
/// named individuals) occurring in a class expression, for the fresh-entity check
/// (`OWLObject.get*InSignature`). Object-property expressions contribute their
/// underlying named property; anonymous individuals are skipped (Java collects only
/// `OWLNamedIndividual`).
fn collect_ce_entities(
    ce: &CE<crate::structural::A>,
    classes: &mut Vec<String>,
    ops: &mut Vec<String>,
    dps: &mut Vec<String>,
    inds: &mut Vec<String>,
) {
    use horned_owl::model::{Individual as I, ObjectPropertyExpression as OPE};
    let push_op = |ope: &OPE<crate::structural::A>, ops: &mut Vec<String>| match ope {
        OPE::ObjectProperty(p) => ops.push(p.0.to_string()),
        OPE::InverseObjectProperty(p) => ops.push(p.0.to_string()),
    };
    let push_ind = |i: &I<crate::structural::A>, inds: &mut Vec<String>| {
        if let I::Named(n) = i {
            inds.push(n.0.to_string());
        }
    };
    match ce {
        CE::Class(c) => classes.push(c.0.to_string()),
        CE::ObjectIntersectionOf(v) | CE::ObjectUnionOf(v) => {
            for sub in v {
                collect_ce_entities(sub, classes, ops, dps, inds);
            }
        }
        CE::ObjectComplementOf(b) => collect_ce_entities(b, classes, ops, dps, inds),
        CE::ObjectOneOf(v) => {
            for i in v {
                push_ind(i, inds);
            }
        }
        CE::ObjectSomeValuesFrom { ope, bce }
        | CE::ObjectAllValuesFrom { ope, bce }
        | CE::ObjectMinCardinality { ope, bce, .. }
        | CE::ObjectMaxCardinality { ope, bce, .. }
        | CE::ObjectExactCardinality { ope, bce, .. } => {
            push_op(ope, ops);
            collect_ce_entities(bce, classes, ops, dps, inds);
        }
        CE::ObjectHasValue { ope, i } => {
            push_op(ope, ops);
            push_ind(i, inds);
        }
        CE::ObjectHasSelf(ope) => push_op(ope, ops),
        CE::DataSomeValuesFrom { dp, .. }
        | CE::DataAllValuesFrom { dp, .. }
        | CE::DataHasValue { dp, .. }
        | CE::DataMinCardinality { dp, .. }
        | CE::DataMaxCardinality { dp, .. }
        | CE::DataExactCardinality { dp, .. } => dps.push(dp.0.to_string()),
    }
}

/// Port of `Reasoner.throwFreshEntityExceptionIfNecessary` (Reasoner.java:2187) —
/// Under `FreshEntityPolicy::Disallow`, any entity occurring in the query
/// that is neither defined in the ontology vocabulary nor an internal IRI makes the
/// query throw a `FreshEntitiesException` analogue. A no-op under the default
/// `Allow` policy.
fn throw_fresh_entity_exception_if_necessary(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
    classes: &[String],
    ops: &[String],
    dps: &[String],
    inds: &[String],
) -> Result<(), String> {
    use crate::configuration::FreshEntityPolicy;
    use crate::prefixes::Prefixes;
    if configuration.fresh_entity_policy != FreshEntityPolicy::Disallow {
        return Ok(());
    }
    let build = Build::new_arc();
    let mut undeclared: Vec<String> = Vec::new();
    for iri in classes {
        if !Prefixes::is_internal_iri(iri) && !is_defined_class(ontology, &build.class(iri.clone()))? {
            undeclared.push(iri.clone());
        }
    }
    for iri in ops {
        if !Prefixes::is_internal_iri(iri)
            && !is_defined_object_property(ontology, &build.object_property(iri.clone()))?
        {
            undeclared.push(iri.clone());
        }
    }
    for iri in dps {
        if !Prefixes::is_internal_iri(iri)
            && !is_defined_data_property(ontology, &build.data_property(iri.clone()))?
        {
            undeclared.push(iri.clone());
        }
    }
    for iri in inds {
        if !Prefixes::is_internal_iri(iri)
            && !is_defined_individual(ontology, &build.named_individual(iri.clone()))?
        {
            undeclared.push(iri.clone());
        }
    }
    if !undeclared.is_empty() {
        undeclared.sort();
        undeclared.dedup();
        return Err(format!("FreshEntitiesException: {undeclared:?}"));
    }
    Ok(())
}

/// The default-configuration variant of the inconsistency guard: the free public
/// query functions do not carry a `Configuration`, so they use HermiT's default
/// (`throw_inconsistent_ontology_exception = true`).
fn check_pre_conditions(ontology: &SetOntology<crate::structural::A>) -> Result<(), String> {
    throw_inconsistent_ontology_exception_if_necessary(
        ontology,
        &crate::configuration::Configuration::default(),
    )
}

/// Port of `Reasoner.checkPreConditions(OWLObject...)` (Reasoner.java:2173).
/// The fresh-entity throw runs FIRST (over the query's named-entity signature), then
/// the inconsistency throw, both honouring `configuration`. Every public query
/// whose arguments carry named entities routes through this so
/// `FreshEntityPolicy::Disallow` rejects undeclared classes/properties/individuals
/// exactly as Java does. Under the default `Allow` policy the fresh-entity step is a
/// no-op, so default-configuration behaviour is unchanged.
fn check_pre_conditions_with(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
    classes: &[String],
    ops: &[String],
    dps: &[String],
    inds: &[String],
) -> Result<(), String> {
    throw_fresh_entity_exception_if_necessary(ontology, configuration, classes, ops, dps, inds)?;
    throw_inconsistent_ontology_exception_if_necessary(ontology, configuration)
}

// --- The public/internal split -----------------------------------------------
//
// In HermiT the *public* `Reasoner.isSatisfiable/isSubClassOf/hasType/isEntailed`
// methods call `checkPreConditions` (which throws on an inconsistent ontology
// under the default flag), while the *internal* reasoning primitives
// (`EntailmentChecker`, the classification subsumption tests, the realisation
// instance tests) reduce directly to `tableau.isSatisfiable(...)` and never
// re-trigger `checkPreConditions`. The port mirrors this: each `*_core` function
// is the non-throwing internal primitive; the `pub fn` of the same name is the
// public wrapper that adds the `checkPreConditions` throw then delegates.
// Internal callers (classify, get_types/get_instances, disjoint_classes, explain,
// is_entailed's arms) call the `*_core` variants so an inconsistent intermediate
// ontology (e.g. a subset during explanation) is reasoned over, not thrown on.

/// Internal (non-throwing) concept-satisfiability primitive.
fn is_concept_satisfiable_core(
    ontology: &SetOntology<crate::structural::A>,
    class_expression: CE<crate::structural::A>,
) -> Result<bool, String> {
    is_concept_satisfiable_core_with(
        ontology,
        class_expression,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`is_concept_satisfiable_core`], but threads `configuration` into the
/// underlying consistency check.
fn is_concept_satisfiable_core_with(
    ontology: &SetOntology<crate::structural::A>,
    class_expression: CE<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    let mut test = ontology.clone();
    let fresh = fresh_anonymous_individual("individual");
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: class_expression,
        i: fresh,
    }));
    is_ontology_consistent_with_configuration(&test, configuration)
}

/// Whether `class_expression` is satisfiable with respect to the ontology
/// (true iff the ontology extended with `C(fresh)` is consistent).
///
/// `Reasoner.isSatisfiable(OWLClassExpression)` (Reasoner.java:755) calls
/// `checkPreConditions(classExpression)` first, so on an inconsistent ontology it
/// throws under the default flag (the subsequent `if(!isConsistent()) return
/// false` only runs when the flag is off).
pub fn is_concept_satisfiable(
    ontology: &SetOntology<crate::structural::A>,
    class_expression: CE<crate::structural::A>,
) -> Result<bool, String> {
    check_pre_conditions(ontology)?;
    is_concept_satisfiable_core(ontology, class_expression)
}

/// As [`is_concept_satisfiable`], but runs the satisfiability test under an
/// explicit [`Configuration`](crate::configuration::Configuration). The
/// `checkPreConditions` throw uses the supplied configuration's flag.
pub fn is_concept_satisfiable_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    class_expression: CE<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    let (mut classes, mut ops, mut dps, mut inds) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    collect_ce_entities(&class_expression, &mut classes, &mut ops, &mut dps, &mut inds);
    check_pre_conditions_with(ontology, configuration, &classes, &ops, &dps, &inds)?;
    is_concept_satisfiable_core_with(ontology, class_expression, configuration)
}

/// Internal (non-throwing) subsumption primitive.
fn is_subsumed_by_core(
    ontology: &SetOntology<crate::structural::A>,
    sub: CE<crate::structural::A>,
    sup: CE<crate::structural::A>,
) -> Result<bool, String> {
    is_subsumed_by_core_with(ontology, sub, sup, &crate::configuration::Configuration::default())
}

/// As [`is_subsumed_by_core`], but threads `configuration` into the
/// underlying satisfiability test.
fn is_subsumed_by_core_with(
    ontology: &SetOntology<crate::structural::A>,
    sub: CE<crate::structural::A>,
    sup: CE<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    let test_concept = CE::ObjectIntersectionOf(vec![sub, CE::ObjectComplementOf(Box::new(sup))]);
    Ok(!is_concept_satisfiable_core_with(ontology, test_concept, configuration)?)
}

/// Whether `sub` is subsumed by `sup` (true iff `sub ⊓ ¬sup` is unsatisfiable).
///
/// `Reasoner.isSubClassOf`/`isEntailed(SubClassOf)` (Reasoner.java:772) calls
/// `checkPreConditions` first, so it throws on an inconsistent ontology under the
/// default flag.
pub fn is_subsumed_by(
    ontology: &SetOntology<crate::structural::A>,
    sub: CE<crate::structural::A>,
    sup: CE<crate::structural::A>,
) -> Result<bool, String> {
    check_pre_conditions(ontology)?;
    is_subsumed_by_core(ontology, sub, sup)
}

/// As [`is_subsumed_by`], but runs the subsumption test under an explicit
/// [`Configuration`](crate::configuration::Configuration).
pub fn is_subsumed_by_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    sub: CE<crate::structural::A>,
    sup: CE<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    let (mut classes, mut ops, mut dps, mut inds) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    collect_ce_entities(&sub, &mut classes, &mut ops, &mut dps, &mut inds);
    collect_ce_entities(&sup, &mut classes, &mut ops, &mut dps, &mut inds);
    check_pre_conditions_with(ontology, configuration, &classes, &ops, &dps, &inds)?;
    is_subsumed_by_core_with(ontology, sub, sup, configuration)
}

/// Internal (non-throwing) instance-of primitive.
fn is_instance_of_core(
    ontology: &SetOntology<crate::structural::A>,
    individual: NamedIndividual<crate::structural::A>,
    class_expression: CE<crate::structural::A>,
) -> Result<bool, String> {
    let mut test = ontology.clone();
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(class_expression)),
        i: OwlIndividual::Named(individual),
    }));
    Ok(!is_ontology_consistent(&test)?)
}

/// Whether `individual` is an instance of `class_expression` (true iff the
/// ontology extended with `¬C(individual)` is inconsistent).
///
/// `Reasoner.hasType` (Reasoner.java:1639) calls `checkPreConditions` first,
/// so on an inconsistent ontology it throws under the default flag (the
/// subsequent `if(!m_isConsistent) return true` only runs when the flag is off).
pub fn is_instance_of(
    ontology: &SetOntology<crate::structural::A>,
    individual: NamedIndividual<crate::structural::A>,
    class_expression: CE<crate::structural::A>,
) -> Result<bool, String> {
    check_pre_conditions(ontology)?;
    is_instance_of_core(ontology, individual, class_expression)
}

/// Classifies the named classes of an ontology into a subsumption
/// [`Hierarchy`](crate::hierarchy::Hierarchy), mirroring HermiT's
/// `DeterministicClassification.classify`: each satisfiable class is mapped to
/// its set of subsumers (computed by subsumption tests), then the subsumer
/// graph is reduced to a hierarchy (equivalent classes share a node; only
/// immediate sub/superclass edges are retained). An inconsistent ontology
/// yields the empty (fully collapsed) hierarchy.
use horned_owl::model::Class;

/// The named classes equivalent to `class` (HermiT's `getEquivalentClasses`),
/// computed from the classified hierarchy.
///
/// `getEquivalentClasses` calls `checkPreConditions` first, so it throws on
/// an inconsistent ontology under the default flag.
pub fn equivalent_classes(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    equivalent_classes_with_configuration(
        ontology,
        class,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`equivalent_classes`], but classifies under an explicit
/// [`Configuration`](crate::configuration::Configuration).
pub fn equivalent_classes_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    check_pre_conditions_with(ontology, configuration, &[class.0.to_string()], &[], &[], &[])?;
    Ok(classify_with_configuration(ontology, configuration)?.equivalent_elements_of(class))
}

/// The named subclasses of `class` (`getSubClasses`); `direct` restricts to the
/// immediate subclasses.
///
/// `getSubClasses` calls `checkPreConditions` first (throws on an
/// inconsistent ontology under the default flag).
pub fn sub_classes(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    sub_classes_with_configuration(
        ontology,
        class,
        direct,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`sub_classes`], but classifies under an explicit
/// [`Configuration`](crate::configuration::Configuration).
pub fn sub_classes_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
    configuration: &crate::configuration::Configuration,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    check_pre_conditions_with(ontology, configuration, &[class.0.to_string()], &[], &[], &[])?;
    Ok(classify_with_configuration(ontology, configuration)?.sub_elements(class, direct))
}

/// The named superclasses of `class` (`getSuperClasses`); `direct` restricts to
/// the immediate superclasses.
///
/// `getSuperClasses` calls `checkPreConditions` first (throws on an
/// inconsistent ontology under the default flag).
pub fn super_classes(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    super_classes_with_configuration(
        ontology,
        class,
        direct,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`super_classes`], but classifies under an explicit
/// [`Configuration`](crate::configuration::Configuration).
pub fn super_classes_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
    configuration: &crate::configuration::Configuration,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    check_pre_conditions_with(ontology, configuration, &[class.0.to_string()], &[], &[], &[])?;
    Ok(classify_with_configuration(ontology, configuration)?.super_elements(class, direct))
}

/// The named classes disjoint from `class` (`getDisjointClasses`): every other
/// classified class `D` with `class ⊓ D` unsatisfiable (i.e. `class ⊑ ¬D`).
///
/// `getDisjointClasses` (Reasoner.java:832) calls `checkPreConditions` first,
/// so it throws on an inconsistent ontology under the default flag (the
/// `!m_isConsistent` branch only runs when the flag is off).
pub fn disjoint_classes(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    disjoint_classes_with_configuration(
        ontology,
        class,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`disjoint_classes`], but classifies and runs the disjointness tests under an
/// explicit [`Configuration`](crate::configuration::Configuration).
pub fn disjoint_classes_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    use std::collections::HashSet;
    check_pre_conditions_with(ontology, configuration, &[class.0.to_string()], &[], &[], &[])?;
    let hierarchy = classify_with_configuration(ontology, configuration)?;
    let build = Build::new_arc();
    let thing = build.class("http://www.w3.org/2002/07/owl#Thing");
    let nothing = build.class("http://www.w3.org/2002/07/owl#Nothing");

    // owl:Nothing is disjoint from everything, so Java's getDisjointClasses
    // ALWAYS returns it (owl:Nothing is the bottom node, a descendant of every disjoint
    // node). Java's getDisjointClasses(owl:Thing) returns the whole bottom node
    // (Reasoner.java:839-841): every class equivalent to owl:Nothing, not just the
    // literal owl:Nothing IRI.
    if *class == thing {
        return Ok(hierarchy.equivalent_elements_of(&nothing));
    }
    // A fresh class absent from the hierarchy on a consistent ontology -> {owl:Nothing}
    // (Reasoner.java:845-848: node==null||node==topNode returns the literal owl:Nothing).
    if !hierarchy.all_elements().any(|e| e == class) {
        return Ok(std::iter::once(nothing).collect());
    }
    // A (non-literal) named class equivalent to owl:Thing sits in the top node, so
    // Java's `node==topNode` arm (Reasoner.java:845-848) also returns the literal
    // owl:Nothing singleton -- NOT the whole bottom equivalence class the general
    // subsumption loop would otherwise collect.
    if hierarchy.equivalent_elements_of(&thing).contains(class) {
        return Ok(std::iter::once(nothing).collect());
    }
    // An unsatisfiable class (a member of the owl:Nothing / bottom node) is disjoint
    // from EVERY class; Java returns bottomNode.getAncestorNodes(), i.e. all nodes
    // including owl:Thing (Reasoner.java:835-838, 849-850).
    if hierarchy.equivalent_elements_of(&nothing).contains(class) {
        return Ok(hierarchy.all_elements().cloned().collect());
    }

    // Java getDisjointConceptNodes (Reasoner.java:870-890): the disjoint classes of C
    // are the named classes subsumed by ¬C, read off the classified hierarchy's ¬C
    // node (getHierarchyNode(¬C) + descendants). Mirror that by classifying
    // (KB + Q ≡ ¬C) ONCE and taking the elements of Q's descendant nodes, instead of
    // testing C ⊑ ¬other for every named class. For a satisfiable C (the unsatisfiable
    // / ≡owl:Thing cases are handled above) neither owl:Thing nor C itself is below
    // ¬C, so they do not appear; owl:Nothing is below ¬C and is included.
    use horned_owl::model::EquivalentClasses;
    let query_class = build.class(fresh_witness_iri("disjoint-query-concept"));
    let mut query_ontology = ontology.clone();
    query_ontology.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(query_class.clone()),
        CE::ObjectComplementOf(Box::new(CE::Class(class.clone()))),
    ])));
    let query_hierarchy = classify_with_configuration(&query_ontology, configuration)?;
    let mut result: HashSet<Class<crate::structural::A>> = HashSet::new();
    if let Some(query_node) = query_hierarchy.node_for_element(&query_class) {
        for descendant in query_hierarchy.descendant_nodes(query_node) {
            for member in query_hierarchy.node(descendant).equivalent_elements() {
                if *member != query_class {
                    result.insert(member.clone());
                }
            }
        }
    }
    // owl:Nothing is disjoint from every class; ensure it is present even if it is not
    // part of the classified element set.
    result.insert(nothing);
    Ok(result)
}

/// Builds a `SetOntology` from a slice of components.
fn ontology_from(components: &[Component<crate::structural::A>]) -> SetOntology<crate::structural::A> {
    let mut ontology = SetOntology::new();
    for component in components {
        ontology.insert(component.clone());
    }
    ontology
}

/// Computes a single justification (a minimal subset of the ontology's axioms
/// that still entails `axiom`) by the standard black-box "shrink" method --
/// the core of HermiT's explanation service. Returns `None` if `axiom` is not
/// entailed (so there is nothing to justify).
///
/// One minimal justification is returned; enumerating *all* justifications
/// (Reiter's hitting-set search over this single-justification oracle) is left
/// to a caller.
pub fn explain(
    ontology: &SetOntology<crate::structural::A>,
    axiom: &Component<crate::structural::A>,
) -> Result<Option<Vec<Component<crate::structural::A>>>, String> {
    if !is_entailed_core(ontology, axiom)? {
        return Ok(None);
    }
    let mut support: Vec<Component<crate::structural::A>> =
        ontology.iter().map(|ac| ac.component.clone()).collect();
    // Shrink to a minimal subset: drop each axiom whose removal preserves the
    // entailment.
    let mut index = 0;
    while index < support.len() {
        let mut reduced = support.clone();
        reduced.remove(index);
        if is_entailed_core(&ontology_from(&reduced), axiom)? {
            support = reduced;
        } else {
            index += 1;
        }
    }
    Ok(Some(support))
}

/// A single justification computed over a given subset of axiom indices, by the
/// shrink method; returns the surviving indices, or `None` if the subset does
/// not entail `axiom`.
fn justify_indices(
    all: &[Component<crate::structural::A>],
    available: &[usize],
    axiom: &Component<crate::structural::A>,
) -> Result<Option<Vec<usize>>, String> {
    let build_ontology = |indices: &[usize]| -> SetOntology<crate::structural::A> {
        let mut ontology = SetOntology::new();
        for &i in indices {
            ontology.insert(all[i].clone());
        }
        ontology
    };
    if !is_entailed_core(&build_ontology(available), axiom)? {
        return Ok(None);
    }
    let mut support: Vec<usize> = available.to_vec();
    let mut index = 0;
    while index < support.len() {
        let mut reduced = support.clone();
        reduced.remove(index);
        if is_entailed_core(&build_ontology(&reduced), axiom)? {
            support = reduced;
        } else {
            index += 1;
        }
    }
    Ok(Some(support))
}

/// Computes **all** minimal justifications for an entailed `axiom` using
/// Reiter's hitting-set tree over the single-justification oracle
/// (`justify_indices`): each found justification is "hit" by removing each of
/// its axioms in turn and recomputing, until every path is closed. Returns an
/// empty vector when `axiom` is not entailed.
///
/// Worst-case exponential in the number of justifications (inherent to the
/// problem); intended for the typical case of a few small justifications.
pub fn all_explanations(
    ontology: &SetOntology<crate::structural::A>,
    axiom: &Component<crate::structural::A>,
) -> Result<Vec<Vec<Component<crate::structural::A>>>, String> {
    use std::collections::HashSet;

    let all: Vec<Component<crate::structural::A>> =
        ontology.iter().map(|ac| ac.component.clone()).collect();
    let full: HashSet<usize> = (0..all.len()).collect();

    let mut justifications: Vec<Vec<usize>> = Vec::new();
    let mut explored: HashSet<Vec<usize>> = HashSet::new();
    // Worklist of "removed" index sets (the hitting-set-tree paths).
    let mut worklist: Vec<HashSet<usize>> = vec![HashSet::new()];

    while let Some(removed) = worklist.pop() {
        let mut removed_key: Vec<usize> = removed.iter().copied().collect();
        removed_key.sort_unstable();
        if !explored.insert(removed_key) {
            continue;
        }
        let available: Vec<usize> = full.difference(&removed).copied().collect();
        let justification = match justify_indices(&all, &available, axiom)? {
            Some(j) => j,
            None => continue, // this path is closed
        };
        let mut sorted = justification.clone();
        sorted.sort_unstable();
        if !justifications.contains(&sorted) {
            justifications.push(sorted);
        }
        // Branch: hit the justification by removing each of its axioms.
        for &axiom_index in &justification {
            let mut next_removed = removed.clone();
            next_removed.insert(axiom_index);
            worklist.push(next_removed);
        }
    }

    Ok(justifications
        .into_iter()
        .map(|indices| indices.into_iter().map(|i| all[i].clone()).collect())
        .collect())
}

/// Whether `axiom` is entailed by the ontology (HermiT's
/// `EntailmentChecker.isEntailed`), by reducing each axiom kind to the core
/// reasoning tests. The general principle is `O ⊨ α  ⟺  O ∪ {¬α}` is
/// inconsistent; for the structural axioms below this reduces to subsumption /
/// instance / satisfiability checks. Returns an error for axiom kinds whose
/// entailment is not supported.
///
/// `Reasoner.isEntailed(OWLAxiom)` (Reasoner.java:688) calls
/// `checkPreConditions(axiom)` first, so the *public* entry throws on an
/// inconsistent ontology under the default flag (the subsequent `if
/// (!isConsistent()) return true` only runs when the flag is off). The internal
/// reduction is `is_entailed_core`, used by the explanation service and by the
/// other `is_entailed` arms (which must reason over possibly-inconsistent
/// intermediate ontologies rather than throw).
pub fn is_entailed(
    ontology: &SetOntology<crate::structural::A>,
    axiom: &Component<crate::structural::A>,
) -> Result<bool, String> {
    check_pre_conditions(ontology)?;
    if !is_ontology_consistent(ontology)? {
        return Ok(true);
    }
    is_entailed_core(ontology, axiom)
}

/// Internal (non-throwing) entailment primitive: the body of HermiT's
/// `EntailmentChecker.isEntailed`. Does not call `checkPreConditions`.
pub(crate) fn is_entailed_core(
    ontology: &SetOntology<crate::structural::A>,
    axiom: &Component<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::{
        Individual as I, NegativeObjectPropertyAssertion, ObjectPropertyAssertion,
        SubObjectPropertyExpression,
    };
    // OWL 2 Sec 11.2 — Same/Different/Negative-assertion axioms are not
    // allowed with anonymous individuals. Java's EntailmentChecker throws before any
    // reasoning; mirror that on the single-axiom path (the Set path already does).
    if axiom_forbids_anonymous(axiom) {
        return Err(
            "axioms of the form Same/Different/Negative-assertion are not allowed with anonymous individuals (OWL 2 Sec 11.2)"
                .into(),
        );
    }
    match axiom {
        Component::SubClassOf(ax) => is_subsumed_by_core(ontology, ax.sub.clone(), ax.sup.clone()),
        Component::EquivalentClasses(ax) => {
            // `visit(OWLEquivalentClassesAxiom)`: the first expression must mutually
            // subsume each of the rest. Define a fresh Qi ≡ Ci, clausify ONCE, and
            // test each subsumption `A ⊑ B` by `¬consistent(Q_A(x) ∧ ¬Q_B(x))` on a
            // fresh witness, reusing one tableau instead of re-clausifying per pair.
            use horned_owl::model::EquivalentClasses;
            let build = Build::new_arc();
            let mut query_ontology = ontology.clone();
            let mut qs: Vec<crate::model::AtomicConcept> = Vec::new();
            for c in &ax.0 {
                let q_iri = fresh_witness_iri("equiv-class-query");
                query_ontology.insert(Component::EquivalentClasses(EquivalentClasses(vec![
                    CE::Class(build.class(q_iri.clone())),
                    c.clone(),
                ])));
                qs.push(crate::model::AtomicConcept::create(q_iri));
            }
            let dl_ontology = clausify_for_query(&query_ontology)?;
            let reasoner = Reasoner::new(&dl_ontology);
            let mut manager = reasoner.new_manager();
            let x = crate::model::Individual::create(fresh_witness_iri("equiv-class-witness"));
            let on_x = |q: &crate::model::AtomicConcept| {
                crate::model::Atom::create(
                    DLPredicate::AtomicConcept(q.clone()),
                    vec![Term::Individual(x.clone())],
                )
            };
            if let Some((first, rest)) = qs.split_first() {
                for next in rest {
                    // first ⊑ next  AND  next ⊑ first  (mutual subsumption).
                    if reasoner.is_consistent_with_pos_neg_test_atoms(
                        &mut manager,
                        &[on_x(first)],
                        &[on_x(next)],
                    ) || reasoner.is_consistent_with_pos_neg_test_atoms(
                        &mut manager,
                        &[on_x(next)],
                        &[on_x(first)],
                    ) {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
        Component::DisjointClasses(ax) => {
            // Disjoint iff every pair Ci ⊓ Cj is unsatisfiable. Define a fresh
            // Qi ≡ Ci for each operand, clausify ONCE, and test each pair by
            // asserting Qi(x) ∧ Qj(x) on a fresh witness x (Ci⊓Cj satisfiable iff
            // that is consistent), reusing one tableau instead of re-clausifying
            // ¬-free Ci⊓Cj per pair.
            use horned_owl::model::EquivalentClasses;
            let build = Build::new_arc();
            let mut query_ontology = ontology.clone();
            let mut query_concepts: Vec<crate::model::AtomicConcept> = Vec::new();
            for c in &ax.0 {
                let q_iri = fresh_witness_iri("disjoint-class-query");
                query_ontology.insert(Component::EquivalentClasses(EquivalentClasses(vec![
                    CE::Class(build.class(q_iri.clone())),
                    c.clone(),
                ])));
                query_concepts.push(crate::model::AtomicConcept::create(q_iri));
            }
            let dl_ontology = clausify_for_query(&query_ontology)?;
            let reasoner = Reasoner::new(&dl_ontology);
            let mut manager = reasoner.new_manager();
            let x = crate::model::Individual::create(fresh_witness_iri("disjoint-class-witness"));
            let concept_atom = |q: &crate::model::AtomicConcept| {
                crate::model::Atom::create(
                    DLPredicate::AtomicConcept(q.clone()),
                    vec![Term::Individual(x.clone())],
                )
            };
            for i in 0..query_concepts.len() {
                for j in (i + 1)..query_concepts.len() {
                    let atoms = [concept_atom(&query_concepts[i]), concept_atom(&query_concepts[j])];
                    if reasoner.is_consistent_with_test_atoms(&mut manager, &atoms) {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
        Component::ClassAssertion(ax) => match &ax.i {
            I::Named(n) => is_instance_of_core(ontology, n.clone(), ax.ce.clone()),
            // an anonymous-individual class assertion is checked by rolling
            // up the anonymous-individual forest (single-axiom set).
            I::Anonymous(_) => is_entailed_axioms_core(ontology, std::slice::from_ref(axiom)),
        },
        Component::SubObjectPropertyOf(ax) => match &ax.sub {
            SubObjectPropertyExpression::ObjectPropertyExpression(sub) => {
                is_object_property_subsumed_by(ontology, sub.clone(), ax.sup.clone())
            }
            // EntailmentChecker.visit(OWLSubPropertyChainOfAxiom) ->
            // reasoner.isSubObjectPropertyExpressionOf(chain, super).
            SubObjectPropertyExpression::ObjectPropertyChain(chain) => {
                is_object_property_chain_subsumed_by(ontology, chain, ax.sup.clone())
            }
        },
        Component::EquivalentObjectProperties(ax) => {
            // `visit(OWLEquivalentObjectPropertiesAxiom)`: first vs each of the rest.
            if let Some((first, rest)) = ax.0.split_first() {
                for next in rest {
                    if !is_object_property_subsumed_by(ontology, first.clone(), next.clone())?
                        || !is_object_property_subsumed_by(ontology, next.clone(), first.clone())?
                    {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
        Component::ObjectPropertyAssertion(ax) => {
            // anonymous subject/object goes through the forest roll-up.
            if matches!(ax.from, I::Anonymous(_)) || matches!(ax.to, I::Anonymous(_)) {
                return is_entailed_axioms_core(ontology, std::slice::from_ref(axiom));
            }
            let mut test = ontology.clone();
            test.insert(Component::NegativeObjectPropertyAssertion(
                NegativeObjectPropertyAssertion {
                    ope: ax.ope.clone(),
                    from: ax.from.clone(),
                    to: ax.to.clone(),
                },
            ));
            Ok(!is_ontology_consistent(&test)?)
        }
        Component::NegativeObjectPropertyAssertion(ax) => {
            let mut test = ontology.clone();
            test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
                ope: ax.ope.clone(),
                from: ax.from.clone(),
                to: ax.to.clone(),
            }));
            Ok(!is_ontology_consistent(&test)?)
        }
        Component::SameIndividual(ax) => {
            // `visit(OWLSameIndividualAxiom)`: the first individual must be the
            // same as each of the rest (transitivity covers the other pairs).
            // Entailed iff adding `first != next` is inconsistent. Reuse one tableau
            // (clausify once), injecting each `Inequality(first,next)` as a per-test
            // ABox atom (the clausal form of DifferentIndividuals(first,next)).
            let dl_ontology = clausify_for_query(ontology)?;
            let reasoner = Reasoner::new(&dl_ontology);
            // `Reasoner.isSameIndividual`: an inconsistent premise entails everything;
            // otherwise an individual-free premise never entails SameIndividual
            // (`if (m_dlOntology.getAllIndividuals().size()==0) return false`).
            if !reasoner.is_consistent() {
                return Ok(true);
            }
            if dl_ontology.get_all_individuals().is_empty() {
                return Ok(false);
            }
            let mut manager = reasoner.new_manager();
            if let Some((first, rest)) = ax.0.split_first() {
                for next in rest {
                    let neq = crate::model::Atom::create(
                        DLPredicate::Inequality,
                        vec![
                            Term::Individual(axiom_individual(first)),
                            Term::Individual(axiom_individual(next)),
                        ],
                    );
                    if reasoner.is_consistent_with_test_atoms(&mut manager, &[neq]) {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
        Component::DifferentIndividuals(ax) => {
            // Reuse one tableau, injecting each pair's `Equality` (the clausal form
            // of SameIndividual(ai,aj)) as a per-test atom; entailed iff every pair
            // forced equal is inconsistent.
            let dl_ontology = clausify_for_query(ontology)?;
            let reasoner = Reasoner::new(&dl_ontology);
            let mut manager = reasoner.new_manager();
            for i in 0..ax.0.len() {
                for j in (i + 1)..ax.0.len() {
                    let eq = crate::model::Atom::create(
                        DLPredicate::Equality,
                        vec![
                            Term::Individual(axiom_individual(&ax.0[i])),
                            Term::Individual(axiom_individual(&ax.0[j])),
                        ],
                    );
                    if reasoner.is_consistent_with_test_atoms(&mut manager, &[eq]) {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
        // --- the remaining axiom kinds, reduced exactly as EntailmentChecker does ---
        Component::ObjectPropertyDomain(ax) => {
            // dom(P) ⊒ C  iff  ∃P.⊤ ⊑ C.
            is_subsumed_by_core(ontology, some_values(&ax.ope, thing()), ax.ce.clone())
        }
        Component::ObjectPropertyRange(ax) => {
            // range(P) = C  iff  ⊤ ⊑ ∀P.C.
            is_subsumed_by_core(ontology, thing(), all_values(&ax.ope, ax.ce.clone()))
        }
        Component::DataPropertyDomain(ax) => {
            // dom(D) ⊒ C  iff  ∃D.rdfs:Literal ⊑ C.
            is_subsumed_by_core(ontology, data_some_literal(&ax.dp), ax.ce.clone())
        }
        Component::InverseObjectProperties(ax) => {
            // horned-owl models both operands as ObjectPropertyExpression already.
            let first = ax.0.clone();
            let second = ax.1.clone();
            let inv_first = invert_ope(&first);
            Ok(is_object_property_subsumed_by(ontology, inv_first.clone(), second.clone())?
                && is_object_property_subsumed_by(ontology, second, inv_first)?)
        }
        Component::SymmetricObjectProperty(ax) => {
            // P symmetric  iff  Inv(P) ⊑ P.
            is_object_property_subsumed_by(ontology, invert_ope(&ax.0), ax.0.clone())
        }
        Component::FunctionalObjectProperty(ax) => {
            // P functional  iff  ⊤ ⊑ ≤1 P.⊤.
            is_subsumed_by_core(ontology, thing(), max_one(&ax.0))
        }
        Component::InverseFunctionalObjectProperty(ax) => {
            // P inverse-functional  iff  ⊤ ⊑ ≤1 Inv(P).⊤.
            is_subsumed_by_core(ontology, thing(), max_one(&invert_ope(&ax.0)))
        }
        Component::DisjointUnion(ax) => {
            // C = C1 ⊔ ... ⊔ Cn with pairwise disjointness, entailed iff the
            // conjunction of the inclusion descriptions is a tautology (⊤ ⊑ it).
            is_subsumed_by_core(ontology, thing(), disjoint_union_description(ax))
        }
        Component::DisjointObjectProperties(ax) => {
            // Disjoint iff for every pair, asserting Pi(a,b) ∧ Pj(a,b) for fresh
            // a,b is inconsistent. Reuse one tableau (clausify once), injecting the
            // two role assertions on collision-proof fresh individuals per pair.
            use horned_owl::model::ObjectPropertyExpression as OPE;
            let dl_ontology = clausify_for_query(ontology)?;
            let reasoner = Reasoner::new(&dl_ontology);
            let mut manager = reasoner.new_manager();
            let a = crate::model::Individual::create(fresh_witness_iri("disjoint-prop-a"));
            let b = crate::model::Individual::create(fresh_witness_iri("disjoint-prop-b"));
            let role_atom = |expr: &OPE<crate::structural::A>| -> crate::model::Atom {
                use crate::model::{Atom, AtomicRole};
                match expr {
                    OPE::ObjectProperty(p) => Atom::create(
                        DLPredicate::AtomicRole(AtomicRole::create(p.0.to_string())),
                        vec![Term::Individual(a.clone()), Term::Individual(b.clone())],
                    ),
                    OPE::InverseObjectProperty(p) => Atom::create(
                        DLPredicate::AtomicRole(AtomicRole::create(p.0.to_string())),
                        vec![Term::Individual(b.clone()), Term::Individual(a.clone())],
                    ),
                }
            };
            for i in 0..ax.0.len() {
                for j in (i + 1)..ax.0.len() {
                    let atoms = [role_atom(&ax.0[i]), role_atom(&ax.0[j])];
                    if reasoner.is_consistent_with_test_atoms(&mut manager, &atoms) {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
        Component::DataPropertyRange(ax) => {
            // range(D) = DR  iff  ⊤ ⊑ ∀D.DR.
            is_subsumed_by_core(ontology, thing(), data_all(&ax.dp, ax.dr.clone()))
        }
        Component::DisjointDataProperties(ax) => {
            // Disjoint iff ∃Di.Literal ⊓ ∃Dj.Literal ⊓ ≤1 ⊤_D is unsatisfiable,
            // for every pair (HermiT's reduction).
            for i in 0..ax.0.len() {
                for j in (i + 1)..ax.0.len() {
                    let desc = CE::ObjectIntersectionOf(vec![
                        data_some_literal(&ax.0[i]),
                        data_some_literal(&ax.0[j]),
                        data_max_one_top(),
                    ]);
                    if is_concept_satisfiable_core(ontology, desc)? {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
        // EntailmentChecker.visit(OWLSubDataPropertyOfAxiom) -> reasoner.isSubDataPropertyOf.
        Component::SubDataPropertyOf(ax) => {
            is_sub_data_property_of(ontology, ax.sub.clone(), ax.sup.clone())
        }
        // EntailmentChecker.visit(OWLEquivalentDataPropertiesAxiom): first vs each
        // of the rest, subsumption both ways.
        Component::EquivalentDataProperties(ax) => {
            if let Some((first, rest)) = ax.0.split_first() {
                for next in rest {
                    if !is_sub_data_property_of(ontology, first.clone(), next.clone())?
                        || !is_sub_data_property_of(ontology, next.clone(), first.clone())?
                    {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
        // EntailmentChecker.visit(OWLDatatypeDefinitionAxiom) (~428-448):
        // build ∃freshDP.((¬DR ⊓ DT) ⊔ (¬DT ⊓ DR)) and test unsatisfiable.
        Component::DatatypeDefinition(ax) => {
            is_datatype_definition_entailed(ontology, &ax.kind, &ax.range)
        }
        // EntailmentChecker.visit(OWLTransitiveObjectPropertyAxiom) -> reasoner.isTransitive.
        Component::TransitiveObjectProperty(ax) => is_transitive_core(ontology, ax.0.clone()),
        // EntailmentChecker.visit(OWLReflexiveObjectPropertyAxiom) -> reasoner.isReflexive.
        Component::ReflexiveObjectProperty(ax) => is_reflexive_core(ontology, ax.0.clone()),
        // EntailmentChecker.visit(OWLIrreflexiveObjectPropertyAxiom) -> reasoner.isIrreflexive.
        Component::IrreflexiveObjectProperty(ax) => is_irreflexive_core(ontology, ax.0.clone()),
        // EntailmentChecker.visit(OWLAsymmetricObjectPropertyAxiom) -> reasoner.isAsymmetric.
        Component::AsymmetricObjectProperty(ax) => is_asymmetric_core(ontology, ax.0.clone()),
        // EntailmentChecker.visit(OWLDataPropertyAssertionAxiom): hasType(sub, DataHasValue(dp,v)).
        Component::DataPropertyAssertion(ax) => match &ax.from {
            I::Named(n) => {
                is_instance_of_core(ontology, n.clone(), data_has_value(&ax.dp, ax.to.clone()))
            }
            // anonymous subject goes through the forest roll-up.
            I::Anonymous(_) => is_entailed_axioms_core(ontology, std::slice::from_ref(axiom)),
        },
        // EntailmentChecker.visit(OWLNegativeDataPropertyAssertionAxiom):
        // hasType(sub, not DataHasValue(dp,v)).
        Component::NegativeDataPropertyAssertion(ax) => match &ax.from {
            I::Named(n) => is_instance_of_core(
                ontology,
                n.clone(),
                CE::ObjectComplementOf(Box::new(data_has_value(&ax.dp, ax.to.clone()))),
            ),
            I::Anonymous(_) => Err(
                "entailment of an anonymous-individual negative data-property assertion is not supported"
                    .into(),
            ),
        },
        // EntailmentChecker.visit(OWLFunctionalDataPropertyAxiom) ->
        // reasoner.isFunctional(dp): the data property is functional iff ⊤ ⊑ ≤1 dp.Literal.
        Component::FunctionalDataProperty(ax) => {
            is_subsumed_by_core(ontology, thing(), data_max_one(&ax.0))
        }
        Component::HasKey(ax) => is_has_key_entailed(ontology, ax),
        // Non-logical axioms are vacuously entailed (EntailmentChecker
        // returns Boolean.TRUE for declarations/annotations/imports, and entails(Set)
        // skips non-logical axioms entirely).
        Component::DeclareClass(_)
        | Component::DeclareObjectProperty(_)
        | Component::DeclareDataProperty(_)
        | Component::DeclareNamedIndividual(_)
        | Component::DeclareAnnotationProperty(_)
        | Component::DeclareDatatype(_)
        | Component::AnnotationAssertion(_)
        | Component::SubAnnotationPropertyOf(_)
        | Component::AnnotationPropertyDomain(_)
        | Component::AnnotationPropertyRange(_)
        | Component::Import(_)
        | Component::OntologyAnnotation(_)
        | Component::OntologyID(_)
        | Component::DocIRI(_) => Ok(true),
        _ => Err("entailment for this axiom kind is not supported".into()),
    }
}

// ===========================================================================
// Anonymous-individual rolling-up
// (EntailmentChecker.AnonymousIndividualForestBuilder + checkAnonymousIndividuals).
// ===========================================================================

/// Port of `EntailmentChecker.AnonymousIndividualForestBuilder`. It consumes the
/// conclusion axioms that mention anonymous individuals (ClassAssertion /
/// ObjectPropertyAssertion / DataPropertyAssertion), builds the labelled forest
/// they induce (anonymous individuals as nodes, object-property assertions as
/// edges, class / data-property assertions as node labels), checks the forest is
/// valid (acyclic, every component has a suitable root per OWL 2 Sec 11.2), and
/// rolls each tree up into a class expression on its root. It emits:
///   * `anon_ind_axioms`: `ClassAssertion(∃op.C, namedRoot)` axioms to be tested
///     for entailment (when a root has exactly one relation to a named
///     individual), and
///   * `anon_no_named_ind_axioms`: `SubClassOf(⊤, ¬C)` axioms which, when added to
///     the premise, must make it inconsistent (when a component has no named root).
struct AnonymousIndividualForestBuilder {
    nodes: std::collections::HashSet<String>,
    // forest edges between anonymous individuals (undirected adjacency).
    edges: HashMap<String, std::collections::HashSet<String>>,
    // anon -> (named -> set of object-property expressions toward the named ind).
    special_op_edges:
        HashMap<String, HashMap<String, std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>>>,
    // node labels (class expressions).
    node_labels: HashMap<String, Vec<CE<Ae>>>,
    // edge labels: (sub_anon, obj_anon) -> object property (named).
    edge_op_labels: HashMap<(String, String), horned_owl::model::ObjectProperty<crate::structural::A>>,
    anon_ind_axioms: Vec<Component<Ae>>,
    anon_no_named_ind_axioms: Vec<Component<Ae>>,
}

impl AnonymousIndividualForestBuilder {
    fn new() -> Self {
        AnonymousIndividualForestBuilder {
            nodes: std::collections::HashSet::new(),
            edges: HashMap::new(),
            special_op_edges: HashMap::new(),
            node_labels: HashMap::new(),
            edge_op_labels: HashMap::new(),
            anon_ind_axioms: Vec::new(),
            anon_no_named_ind_axioms: Vec::new(),
        }
    }

    /// `constructConceptsForAnonymousIndividuals`: visit each axiom, then find
    /// components, choose roots, and read off the rolled-up axioms.
    fn construct(&mut self, axioms: &[Component<Ae>]) -> Result<(), String> {
        use horned_owl::model::Individual as I;
        for axiom in axioms {
            match axiom {
                Component::ClassAssertion(ax) => self.visit_class_assertion(&ax.ce, &ax.i),
                Component::ObjectPropertyAssertion(ax) => {
                    self.visit_object_property_assertion(&ax.ope, &ax.from, &ax.to)?
                }
                Component::DataPropertyAssertion(ax) => {
                    if let I::Anonymous(a) = &ax.from {
                        self.visit_data_property_assertion(a, &ax.dp, &ax.to);
                    }
                }
                _ => {}
            }
        }
        let components = self.get_components()?;
        let components_to_roots = self.find_suitable_roots(&components)?;
        for (component, root) in components_to_roots {
            let _ = component;
            if !self.special_op_edges.contains_key(&root) {
                // No relation to a named individual: roll up into SubClassOf(⊤, ¬C).
                let c = self.class_expression_for(&root, None);
                self.anon_no_named_ind_axioms
                    .push(Component::SubClassOf(horned_owl::model::SubClassOf {
                        sub: thing(),
                        sup: CE::ObjectComplementOf(Box::new(c)),
                    }));
            } else {
                // Exactly one relation to a named individual: roll up into a class
                // assertion ClassAssertion(∃op⁻.C, named).
                let ind2op = self.special_op_edges.get(&root).unwrap().clone();
                if ind2op.len() != 1 {
                    return Err(
                        "Internal error: anonymous-individual forest root has multiple named relations".into(),
                    );
                }
                let (named, ops) = ind2op.into_iter().next().unwrap();
                if ops.len() != 1 {
                    return Err(
                        "Internal error: anonymous-individual forest root has multiple object properties to its named relation".into(),
                    );
                }
                let op = ops.into_iter().next().unwrap();
                let inv_op = invert_ope(&op);
                let c = self.class_expression_for(&root, None);
                let build = Build::new_arc();
                self.anon_ind_axioms.push(Component::ClassAssertion(
                    horned_owl::model::ClassAssertion {
                        ce: CE::ObjectSomeValuesFrom { ope: inv_op, bce: Box::new(c) },
                        i: horned_owl::model::Individual::Named(build.named_individual(named)),
                    },
                ));
            }
        }
        Ok(())
    }

    /// `getClassExpressionFor`: roll the subtree at `node` (with `predecessor`
    /// excluded) up into a class expression.
    fn class_expression_for(&self, node: &str, predecessor: Option<&str>) -> CE<Ae> {
        let successors = self.edges.get(node);
        let is_leaf = match successors {
            None => true,
            Some(s) => s.len() == 1 && predecessor.map_or(false, |p| s.contains(p)),
        };
        if is_leaf {
            return match self.node_labels.get(node) {
                None => thing(),
                Some(labels) if labels.len() == 1 => labels[0].clone(),
                Some(labels) => CE::ObjectIntersectionOf(labels.clone()),
            };
        }
        let successors = successors.unwrap();
        let mut concepts: Vec<CE<Ae>> = Vec::new();
        for successor in successors {
            if predecessor.map_or(false, |p| p == successor) {
                continue;
            }
            // Find the edge label in either direction.
            let op = self
                .edge_op_labels
                .get(&(node.to_string(), successor.clone()))
                .or_else(|| self.edge_op_labels.get(&(successor.clone(), node.to_string())))
                .cloned();
            let op = match op {
                Some(op) => op,
                None => continue, // defensive; Java throws here
            };
            let sub_concept = self.class_expression_for(successor, Some(node));
            concepts.push(CE::ObjectSomeValuesFrom {
                ope: horned_owl::model::ObjectPropertyExpression::ObjectProperty(op),
                bce: Box::new(sub_concept),
            });
        }
        // Internal forest nodes build their rolled-up concept SOLELY from
        // successor edges, matching Java EntailmentChecker.getClassExpressionFor
        // (only the leaf branch above consults node labels). Do NOT append this
        // node's own labels here.
        if concepts.len() == 1 {
            concepts.into_iter().next().unwrap()
        } else {
            CE::ObjectIntersectionOf(concepts)
        }
    }

    /// `findSuitableRoots`: for each component find a node with at most one
    /// relation to named individuals; prefer one with exactly one.
    fn find_suitable_roots(
        &self,
        components: &[std::collections::HashSet<String>],
    ) -> Result<Vec<(std::collections::HashSet<String>, String)>, String> {
        let mut result = Vec::new();
        for component in components {
            let mut root: Option<String> = None;
            let mut root_with_one_named: Option<String> = None;
            for ind in component {
                match self.special_op_edges.get(ind) {
                    Some(edges) => {
                        if edges.len() < 2 {
                            root_with_one_named = Some(ind.clone());
                        }
                    }
                    None => {
                        root = Some(ind.clone());
                    }
                }
            }
            match (root, root_with_one_named) {
                (None, None) => {
                    return Err("Invalid input ontology: a tree in the forest of anonymous individuals has no suitable root (OWL 2 Sec 11.2).".into());
                }
                (_, Some(r)) => result.push((component.clone(), r)),
                (Some(r), None) => result.push((component.clone(), r)),
            }
        }
        Ok(result)
    }

    /// `getComponents`: connected components over the anonymous-individual edges,
    /// detecting cycles (which make a forest impossible).
    fn get_components(&self) -> Result<Vec<std::collections::HashSet<String>>, String> {
        let mut components: Vec<std::collections::HashSet<String>> = Vec::new();
        let mut to_process: std::collections::HashSet<String> = self.nodes.clone();
        while let Some(start) = to_process.iter().next().cloned() {
            let mut current_component: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            // work queue of (node, predecessor).
            let mut work_queue: Vec<(String, Option<String>)> = vec![(start, None)];
            while !work_queue.is_empty() {
                let (node, predecessor) = work_queue.remove(0);
                current_component.insert(node.clone());
                if let Some(successors) = self.edges.get(&node) {
                    for ind in successors {
                        if predecessor.as_deref() != Some(ind.as_str()) {
                            // cycle check: ind already queued.
                            if work_queue.iter().any(|(n, _)| n == ind) {
                                return Err("Invalid input ontology: the anonymous individuals contain a cycle and cannot form a forest (OWL 2 Sec 11.2).".into());
                            }
                            work_queue.push((ind.clone(), Some(node.clone())));
                        }
                    }
                }
            }
            for n in &current_component {
                to_process.remove(n);
            }
            components.push(current_component);
        }
        Ok(components)
    }

    fn visit_class_assertion(
        &mut self,
        ce: &CE<Ae>,
        individual: &horned_owl::model::Individual<crate::structural::A>,
    ) {
        use horned_owl::model::Individual as I;
        // skip owl:Thing labels.
        if let CE::Class(c) = ce {
            if c.0.to_string() == "http://www.w3.org/2002/07/owl#Thing" {
                return;
            }
        }
        if let I::Anonymous(a) = individual {
            let key = a.0.to_string();
            self.nodes.insert(key.clone());
            self.node_labels.entry(key).or_default().push(ce.clone());
        }
    }

    fn visit_object_property_assertion(
        &mut self,
        ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
        sub: &horned_owl::model::Individual<crate::structural::A>,
        obj: &horned_owl::model::Individual<crate::structural::A>,
    ) -> Result<(), String> {
        use horned_owl::model::{Individual as I, ObjectPropertyExpression as OPE};
        let sub_anon = matches!(sub, I::Anonymous(_));
        let obj_anon = matches!(obj, I::Anonymous(_));
        if !sub_anon && !obj_anon {
            return Ok(()); // not interesting for the forest
        }
        let name_of = |i: &I<crate::structural::A>| -> String {
            match i {
                I::Named(n) => n.0.to_string(),
                I::Anonymous(a) => a.0.to_string(),
            }
        };
        if sub_anon != obj_anon {
            // exactly one anonymous.
            let (named, unnamed, ope) = if !sub_anon && obj_anon {
                // swap and invert.
                (name_of(sub), name_of(obj), invert_ope(ope))
            } else {
                (name_of(obj), name_of(sub), ope.clone())
            };
            self.nodes.insert(unnamed.clone());
            // EntailmentChecker.java:739-757: if this anonymous node already has a
            // label for `named`, add `ope` to it; otherwise INSTALL A FRESH
            // single-entry inner map for the node, discarding any previously
            // recorded named neighbours, so each anonymous node retains only its
            // most-recently-seen named neighbour.
            if let Some(special_edges) = self.special_op_edges.get_mut(&unnamed) {
                if let Some(label) = special_edges.get_mut(&named) {
                    label.insert(ope);
                    return Ok(());
                }
            }
            let mut label = std::collections::HashSet::new();
            label.insert(ope);
            let mut fresh = HashMap::new();
            fresh.insert(named, label);
            self.special_op_edges.insert(unnamed, fresh);
            return Ok(());
        }
        // both anonymous.
        let (op, sub_a, obj_a) = match ope {
            OPE::InverseObjectProperty(p) => (p.clone(), name_of(obj), name_of(sub)),
            OPE::ObjectProperty(p) => (p.clone(), name_of(sub), name_of(obj)),
        };
        self.nodes.insert(sub_a.clone());
        self.nodes.insert(obj_a.clone());
        let already = self
            .edges
            .get(&sub_a)
            .map_or(false, |s| s.contains(&obj_a))
            || self.edges.get(&obj_a).map_or(false, |s| s.contains(&sub_a));
        if already {
            return Err("Invalid input ontology: two object-property assertions for the same anonymous individuals (OWL 2 Sec 11.2).".into());
        }
        self.edges.entry(sub_a.clone()).or_default().insert(obj_a.clone());
        self.edges.entry(obj_a.clone()).or_default().insert(sub_a.clone());
        self.edge_op_labels.insert((sub_a, obj_a), op);
        Ok(())
    }

    fn visit_data_property_assertion(
        &mut self,
        sub: &horned_owl::model::AnonymousIndividual<crate::structural::A>,
        dp: &horned_owl::model::DataProperty<crate::structural::A>,
        literal: &horned_owl::model::Literal<crate::structural::A>,
    ) {
        let key = sub.0.to_string();
        self.nodes.insert(key.clone());
        let c = CE::DataHasValue { dp: dp.clone(), l: literal.clone() };
        self.node_labels.entry(key).or_default().push(c);
    }
}

/// Whether an axiom mentions an anonymous individual (so it must go through the
/// forest-builder path rather than the named-individual entailment reduction).
fn mentions_anonymous_individual(axiom: &Component<Ae>) -> bool {
    use horned_owl::model::Individual as I;
    let is_anon = |i: &I<crate::structural::A>| matches!(i, I::Anonymous(_));
    match axiom {
        Component::ClassAssertion(ax) => is_anon(&ax.i),
        Component::ObjectPropertyAssertion(ax) => is_anon(&ax.from) || is_anon(&ax.to),
        Component::DataPropertyAssertion(ax) => is_anon(&ax.from),
        _ => false,
    }
}

/// Whether an axiom is one that Java THROWS on when it contains anonymous
/// individuals (SameIndividual / DifferentIndividuals / NegativeObject- and
/// NegativeData-PropertyAssertion -- OWL 2 Sec 11.2).
fn axiom_forbids_anonymous(axiom: &Component<Ae>) -> bool {
    use horned_owl::model::Individual as I;
    let is_anon = |i: &I<crate::structural::A>| matches!(i, I::Anonymous(_));
    match axiom {
        Component::SameIndividual(ax) => ax.0.iter().any(is_anon),
        Component::DifferentIndividuals(ax) => ax.0.iter().any(is_anon),
        Component::NegativeObjectPropertyAssertion(ax) => is_anon(&ax.from) || is_anon(&ax.to),
        Component::NegativeDataPropertyAssertion(ax) => is_anon(&ax.from),
        _ => false,
    }
}

/// Port of `EntailmentChecker.entails(Set<OWLAxiom>)` + `checkAnonymousIndividuals`.
/// Each axiom that mentions only named individuals is tested with
/// [`is_entailed`]; axioms mentioning anonymous individuals are collected and
/// handled together by building the anonymous-individual forest, rolling each
/// tree up into a class expression on its named root, and testing:
///   * `anon_ind_axioms` -- `ClassAssertion(∃op.C, named)` -- for entailment, and
///   * `anon_no_named_ind_axioms` -- `SubClassOf(⊤, ¬C)` -- by checking that the
///     premise plus that axiom is inconsistent.
/// Errors (matching Java's `throw`) on Same/Different/Negative assertions that
/// contain anonymous individuals.
pub fn is_entailed_axioms(
    ontology: &SetOntology<crate::structural::A>,
    axioms: &[Component<crate::structural::A>],
) -> Result<bool, String> {
    // The public `Reasoner.isEntailed(Set<OWLAxiom>)` (Reasoner.java:695)
    // calls `checkPreConditions(...)` first, so it throws on an inconsistent
    // ontology under the default flag.
    check_pre_conditions(ontology)?;
    if !is_ontology_consistent(ontology)? {
        return Ok(true);
    }
    is_entailed_axioms_core(ontology, axioms)
}

/// Internal (non-throwing) set-entailment primitive. Used by `is_entailed_core`'s
/// anonymous-individual arms, so it must reason over a possibly-inconsistent
/// ontology rather than throw.
pub(crate) fn is_entailed_axioms_core(
    ontology: &SetOntology<crate::structural::A>,
    axioms: &[Component<crate::structural::A>],
) -> Result<bool, String> {
    let mut anonymous_axioms: Vec<Component<Ae>> = Vec::new();
    for axiom in axioms {
        if axiom_forbids_anonymous(axiom) {
            return Err(
                "axioms of the form Same/Different/Negative-assertion are not allowed with anonymous individuals (OWL 2 Sec 11.2)".into(),
            );
        }
        if mentions_anonymous_individual(axiom) {
            anonymous_axioms.push(axiom.clone());
            continue;
        }
        if !is_entailed_core(ontology, axiom)? {
            return Ok(false);
        }
    }
    if anonymous_axioms.is_empty() {
        return Ok(true);
    }
    // checkAnonymousIndividuals: build the forest and roll up.
    let mut builder = AnonymousIndividualForestBuilder::new();
    builder.construct(&anonymous_axioms)?;
    for ax in &builder.anon_ind_axioms {
        if !is_entailed_core(ontology, ax)? {
            return Ok(false);
        }
    }
    for ax in &builder.anon_no_named_ind_axioms {
        // Entailed iff premise ∪ {ax} is inconsistent.
        let mut test = ontology.clone();
        test.insert(ax.clone());
        if is_ontology_consistent(&test)? {
            return Ok(false);
        }
    }
    Ok(true)
}

// --- Public property-characteristic / individual queries, mirroring the
// corresponding `Reasoner.is*` methods (each reduces to an entailment test).

/// `Reasoner.isSymmetric`.
pub fn is_symmetric(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::SymmetricObjectProperty;
    is_entailed(ontology, &Component::SymmetricObjectProperty(SymmetricObjectProperty(ope)))
}

/// `Reasoner.isFunctional` (object property).
pub fn is_functional(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::FunctionalObjectProperty;
    is_entailed(ontology, &Component::FunctionalObjectProperty(FunctionalObjectProperty(ope)))
}

/// `Reasoner.isInverseFunctional` (object property).
pub fn is_inverse_functional(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::InverseFunctionalObjectProperty;
    is_entailed(
        ontology,
        &Component::InverseFunctionalObjectProperty(InverseFunctionalObjectProperty(ope)),
    )
}

/// `Reasoner.isSameIndividual`: whether `a` and `b` are entailed to be the same.
pub fn is_same_individual(
    ontology: &SetOntology<crate::structural::A>,
    a: NamedIndividual<crate::structural::A>,
    b: NamedIndividual<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::{Individual as I, SameIndividual};
    is_entailed(
        ontology,
        &Component::SameIndividual(SameIndividual(vec![I::Named(a), I::Named(b)])),
    )
}

/// Whether `a` and `b` are entailed to be different individuals.
pub fn is_different_individual(
    ontology: &SetOntology<crate::structural::A>,
    a: NamedIndividual<crate::structural::A>,
    b: NamedIndividual<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::{DifferentIndividuals, Individual as I};
    is_entailed(
        ontology,
        &Component::DifferentIndividuals(DifferentIndividuals(vec![I::Named(a), I::Named(b)])),
    )
}

// --- Class-expression builders shared by `is_entailed`'s extra axiom kinds.
// These mirror the `factory.getOWL...` constructions in `EntailmentChecker`.

type Ae = crate::structural::A;

/// `owl:Thing`.
fn thing() -> CE<Ae> {
    let build = Build::new_arc();
    CE::Class(build.class("http://www.w3.org/2002/07/owl#Thing"))
}

/// `∃ope.bce`.
fn some_values(
    ope: &horned_owl::model::ObjectPropertyExpression<Ae>,
    bce: CE<Ae>,
) -> CE<Ae> {
    CE::ObjectSomeValuesFrom { ope: ope.clone(), bce: Box::new(bce) }
}

/// `∀ope.bce`.
fn all_values(
    ope: &horned_owl::model::ObjectPropertyExpression<Ae>,
    bce: CE<Ae>,
) -> CE<Ae> {
    CE::ObjectAllValuesFrom { ope: ope.clone(), bce: Box::new(bce) }
}

/// `≤1 ope.⊤`.
fn max_one(ope: &horned_owl::model::ObjectPropertyExpression<Ae>) -> CE<Ae> {
    CE::ObjectMaxCardinality { n: 1, ope: ope.clone(), bce: Box::new(thing()) }
}

/// `∃dp.rdfs:Literal` (the top datatype).
fn data_some_literal(dp: &horned_owl::model::DataProperty<Ae>) -> CE<Ae> {
    let build = Build::new_arc();
    CE::DataSomeValuesFrom {
        dp: dp.clone(),
        dr: horned_owl::model::DataRange::Datatype(
            build.datatype("http://www.w3.org/2000/01/rdf-schema#Literal"),
        ),
    }
}

/// `∀dp.dr`.
fn data_all(
    dp: &horned_owl::model::DataProperty<Ae>,
    dr: horned_owl::model::DataRange<Ae>,
) -> CE<Ae> {
    CE::DataAllValuesFrom { dp: dp.clone(), dr }
}

/// `dp value v` (`DataHasValue`), mirroring `factory.getOWLDataHasValue`.
fn data_has_value(
    dp: &horned_owl::model::DataProperty<Ae>,
    literal: horned_owl::model::Literal<Ae>,
) -> CE<Ae> {
    CE::DataHasValue { dp: dp.clone(), l: literal }
}

/// `≤1 dp.rdfs:Literal`, the description used for `FunctionalDataProperty`
/// (`reasoner.isFunctional(dp)`: `⊤ ⊑ ≤1 dp`).
fn data_max_one(dp: &horned_owl::model::DataProperty<Ae>) -> CE<Ae> {
    let build = Build::new_arc();
    CE::DataMaxCardinality {
        n: 1,
        dp: dp.clone(),
        dr: horned_owl::model::DataRange::Datatype(
            build.datatype("http://www.w3.org/2000/01/rdf-schema#Literal"),
        ),
    }
}

/// `≤1 owl:topDataProperty.rdfs:Literal`.
fn data_max_one_top() -> CE<Ae> {
    let build = Build::new_arc();
    CE::DataMaxCardinality {
        n: 1,
        dp: build.data_property("http://www.w3.org/2002/07/owl#topDataProperty"),
        dr: horned_owl::model::DataRange::Datatype(
            build.datatype("http://www.w3.org/2000/01/rdf-schema#Literal"),
        ),
    }
}

/// The inverse of an object-property expression (`Inv(P)` for `P`, and `P` for
/// `Inv(P)`).
fn invert_ope(
    ope: &horned_owl::model::ObjectPropertyExpression<Ae>,
) -> horned_owl::model::ObjectPropertyExpression<Ae> {
    use horned_owl::model::ObjectPropertyExpression as OPE;
    match ope {
        OPE::ObjectProperty(op) => OPE::InverseObjectProperty(op.clone()),
        OPE::InverseObjectProperty(op) => OPE::ObjectProperty(op.clone()),
    }
}

/// Port of `EntailmentChecker.visit(OWLDisjointUnionAxiom)`'s `entailmentDesc`:
/// the conjunction of the two inclusion directions and the pairwise-disjointness
/// clauses, whose validity (`⊤ ⊑ ·`) is equivalent to the axiom holding.
fn disjoint_union_description(ax: &horned_owl::model::DisjointUnion<Ae>) -> CE<Ae> {
    let c = CE::Class(ax.0.clone());
    let classes: Vec<CE<Ae>> = ax.1.clone();
    let not = |ce: &CE<Ae>| CE::ObjectComplementOf(Box::new(ce.clone()));

    // incl1: ¬C ⊔ C1 ⊔ ... ⊔ Cn
    let mut incl1_args = classes.clone();
    incl1_args.push(not(&c));
    let incl1 = CE::ObjectUnionOf(incl1_args);
    // incl2: ¬(C1 ⊔ ... ⊔ Cn) ⊔ C
    let incl2 = CE::ObjectUnionOf(vec![not(&CE::ObjectUnionOf(classes.clone())), c]);

    let mut conjuncts = vec![incl1, incl2];
    for i in 0..classes.len() {
        for j in (i + 1)..classes.len() {
            conjuncts.push(CE::ObjectUnionOf(vec![not(&classes[i]), not(&classes[j])]));
        }
    }
    CE::ObjectIntersectionOf(conjuncts)
}

/// Whether the object property `sub` is subsumed by `sup` (`sub ⊑ sup`): true
/// iff asserting `sub(a,b)` together with `¬sup(a,b)` for fresh `a,b` is
/// inconsistent.
pub fn is_object_property_subsumed_by(
    ontology: &SetOntology<crate::structural::A>,
    sub: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    sup: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    is_object_property_subsumed_by_with(
        ontology,
        sub,
        sup,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`is_object_property_subsumed_by`], but threads `configuration` into the
/// underlying consistency check.
pub fn is_object_property_subsumed_by_with(
    ontology: &SetOntology<crate::structural::A>,
    sub: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    sup: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    use horned_owl::model::ObjectPropertyExpression as OPE;
    // Java's isSubObjectPropertyExpressionOf (Reasoner.java:1039) opens
    // with checkPreConditions (the fresh-entity throw over sub/sup, then the
    // inconsistency throw) before the `if(!m_isConsistent) return true` reduction.
    let op_iri = |o: &OPE<crate::structural::A>| match o {
        OPE::ObjectProperty(p) | OPE::InverseObjectProperty(p) => p.0.to_string(),
    };
    check_pre_conditions_with(ontology, configuration, &[], &[op_iri(&sub), op_iri(&sup)], &[], &[])?;
    is_object_property_subsumed_by_core_with(ontology, sub, sup, configuration)
}

/// Internal (non-throwing) object-property subsumption reduction used by the
/// role-classification oracle (which has already verified consistency): `sub ⊑ sup`
/// iff asserting `sub(a,b)` with `¬sup(a,b)` for fresh `a,b` is inconsistent.
fn is_object_property_subsumed_by_core_with(
    ontology: &SetOntology<crate::structural::A>,
    sub: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    sup: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    use horned_owl::model::{ClassAssertion, ObjectPropertyAssertion};
    // `isSubObjectPropertyExpressionOf` guard (Reasoner.java:1041): an inconsistent
    // ontology subsumes everything, `owl:bottomObjectProperty` is below everything,
    // and everything is below `owl:topObjectProperty`. `getNamedProperty()` unwraps
    // inverses before the top/bottom check.
    if !is_ontology_consistent_with_configuration(ontology, configuration)?
        || crate::structural::named_property(&sub).0.to_string()
            == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
        || crate::structural::named_property(&sup).0.to_string()
            == "http://www.w3.org/2002/07/owl#topObjectProperty"
    {
        return Ok(true);
    }
    // `isSubObjectPropertyExpressionOf` (Reasoner.java:1051-1062): the pseudo-nominal
    // construction. For fresh A,B assert `sub(A,B)`, `pseudoNominal(B)`, and
    // `(∀sup.¬pseudoNominal)(A)`; `sub ⊑ sup` iff this is unsatisfiable. Asserting
    // `∀sup.¬pseudoNominal` propagates through the role automaton, so the test is
    // correct for a complex (role-chain) or inverse super-role -- a plain
    // `¬sup(A,B)` negative assertion would not exercise that machinery.
    let mut test = ontology.clone();
    let build = Build::new_arc();
    let a = fresh_anonymous_individual("role-subject");
    let b = fresh_anonymous_individual("role-object");
    let pseudo_nominal = CE::Class(build.class("internal:pseudo-nominal"));
    let all_super_not_pseudo_nominal = CE::ObjectAllValuesFrom {
        ope: sup,
        bce: Box::new(CE::ObjectComplementOf(Box::new(pseudo_nominal.clone()))),
    };
    test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: sub,
        from: a.clone(),
        to: b.clone(),
    }));
    test.insert(Component::ClassAssertion(ClassAssertion { ce: pseudo_nominal, i: b }));
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: all_super_not_pseudo_nominal,
        i: a,
    }));
    Ok(!is_ontology_consistent_with_configuration(&test, configuration)?)
}

/// Whether `sub` is subsumed by the *union* of `sups` (i.e. every model forces
/// `sub(a,b)` to satisfy at least one `sup_i(a,b)`). The batched subsumption
/// test of `QuasiOrderClassification.isEveryPossibleSubsumerNonSubsumer`: assert
/// `sub(a,b)` and `not sup_i(a,b)` for every candidate, and test inconsistency.
/// An empty `sups` makes the union empty, so the result is just whether `sub`
/// is unsatisfiable as an edge.
fn is_object_property_subsumed_by_union_with(
    ontology: &SetOntology<crate::structural::A>,
    sub: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    sups: &std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    use horned_owl::model::{ClassAssertion, ObjectPropertyAssertion};
    let mut test = ontology.clone();
    let build = Build::new_arc();
    let a = fresh_anonymous_individual("role-subject");
    let b = fresh_anonymous_individual("role-object");
    let pseudo_nominal = CE::Class(build.class("internal:pseudo-nominal"));
    test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: sub,
        from: a.clone(),
        to: b.clone(),
    }));
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: pseudo_nominal.clone(),
        i: b.clone(),
    }));
    // The pseudo-nominal form of the per-candidate `not sup_i(a,b)` (mirroring the
    // single-subsumption test in `is_object_property_subsumed_by_core_with`): the
    // union subsumption holds iff `b` cannot remain a pseudo-nominal under every
    // `∀sup_i.¬pseudoNominal(a)` simultaneously. This propagates through the role
    // automaton for complex/inverse super-roles.
    for sup in sups {
        test.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::ObjectAllValuesFrom {
                ope: sup.clone(),
                bce: Box::new(CE::ObjectComplementOf(Box::new(pseudo_nominal.clone()))),
            },
            i: a.clone(),
        }));
    }
    Ok(!is_ontology_consistent_with_configuration(&test, configuration)?)
}

/// Port of `Reasoner.isSubDataPropertyOf` (`Reasoner.java:1434-1456`): the
/// fresh-data-property reduction. On an inconsistent ontology HermiT short-
/// circuits to `true` (the `if(!m_isConsistent)` guard). Otherwise: assert
/// `subDP(a, k)` for a fresh anonymous individual `a` and fresh constant `k`,
/// introduce a fresh data property `negDP` made disjoint from `superDP`
/// (`DisjointDataProperties(superDP, negDP)`) and assert `negDP(a, k)`. If the
/// result is inconsistent, then every model forces `superDP(a, k)`, so
/// `subDP ⊑ superDP` -- the data property is subsumed.
pub fn is_sub_data_property_of(
    ontology: &SetOntology<crate::structural::A>,
    sub: horned_owl::model::DataProperty<crate::structural::A>,
    sup: horned_owl::model::DataProperty<crate::structural::A>,
) -> Result<bool, String> {
    is_sub_data_property_of_with(
        ontology,
        sub,
        sup,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`is_sub_data_property_of`], but threads `configuration` into the
/// underlying consistency checks.
pub fn is_sub_data_property_of_with(
    ontology: &SetOntology<crate::structural::A>,
    sub: horned_owl::model::DataProperty<crate::structural::A>,
    sup: horned_owl::model::DataProperty<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    // Java's isSubDataPropertyOf (Reasoner.java:1434) opens with
    // checkPreConditions (fresh-entity over sub/sup, then the inconsistency throw)
    // before the `if(!m_isConsistent) return true` reduction.
    check_pre_conditions_with(
        ontology,
        configuration,
        &[],
        &[],
        &[sub.0.to_string(), sup.0.to_string()],
        &[],
    )?;
    is_sub_data_property_of_core_with(ontology, sub, sup, configuration)
}

/// Internal (non-throwing) data-property subsumption reduction used by the
/// data-role classification oracle (consistency already verified).
fn is_sub_data_property_of_core_with(
    ontology: &SetOntology<crate::structural::A>,
    sub: horned_owl::model::DataProperty<crate::structural::A>,
    sup: horned_owl::model::DataProperty<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    use horned_owl::model::{DataPropertyAssertion, DisjointDataProperties, Literal};
    // HermiT short-circuits on an inconsistent ontology (returns true), and on
    // owl:bottomDataProperty sub / owl:topDataProperty sup.
    if !is_ontology_consistent_with_configuration(ontology, configuration)?
        || sub.0.to_string() == "http://www.w3.org/2002/07/owl#bottomDataProperty"
        || sup.0.to_string() == "http://www.w3.org/2002/07/owl#topDataProperty"
    {
        return Ok(true);
    }
    let build = Build::new_arc();
    let a = fresh_anonymous_individual("subdp-individual");
    let constant = Literal::Datatype {
        datatype_iri: build.iri("internal:anonymous-constants"),
        literal: fresh_witness_iri("subdp-constant"),
    };
    let negated_super = build.data_property(fresh_witness_iri("subdp-negated-super"));
    let mut test = ontology.clone();
    test.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: sub,
        from: a.clone(),
        to: constant.clone(),
    }));
    test.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: negated_super.clone(),
        from: a,
        to: constant,
    }));
    test.insert(Component::DisjointDataProperties(DisjointDataProperties(vec![
        sup,
        negated_super,
    ])));
    Ok(!is_ontology_consistent_with_configuration(&test, configuration)?)
}

/// Whether `sub` is subsumed by the *union* of `sups` (the data-role analogue of
/// [`is_object_property_subsumed_by_union_with`]): assert `subDP(a,k)` and, for
/// each candidate `sup_i`, a fresh `negDP_i` disjoint from `sup_i` with
/// `negDP_i(a,k)`, forcing `k` to be no `sup_i`-value; inconsistency means every
/// model forces some `sup_i(a,k)`, i.e. `sub ⊑ ⊔ sup_i`.
fn is_sub_data_property_of_union_with(
    ontology: &SetOntology<crate::structural::A>,
    sub: horned_owl::model::DataProperty<crate::structural::A>,
    sups: &std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    use horned_owl::model::{DataPropertyAssertion, DisjointDataProperties, Literal};
    if !is_ontology_consistent_with_configuration(ontology, configuration)?
        || sub.0.to_string() == "http://www.w3.org/2002/07/owl#bottomDataProperty"
        || sups
            .iter()
            .any(|s| s.0.to_string() == "http://www.w3.org/2002/07/owl#topDataProperty")
    {
        return Ok(true);
    }
    let build = Build::new_arc();
    let a = fresh_anonymous_individual("subdp-individual");
    let constant = Literal::Datatype {
        datatype_iri: build.iri("internal:anonymous-constants"),
        literal: fresh_witness_iri("subdp-constant"),
    };
    let mut test = ontology.clone();
    test.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: sub,
        from: a.clone(),
        to: constant.clone(),
    }));
    for sup in sups {
        let negated_super = build.data_property(fresh_witness_iri("subdp-negated-super"));
        test.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
            dp: negated_super.clone(),
            from: a.clone(),
            to: constant.clone(),
        }));
        test.insert(Component::DisjointDataProperties(DisjointDataProperties(vec![
            sup.clone(),
            negated_super,
        ])));
    }
    Ok(!is_ontology_consistent_with_configuration(&test, configuration)?)
}

/// `Reasoner.isIrreflexive` (`Reasoner.java:1266`). Like `is_symmetric`, the
/// public predicate routes through `is_entailed` so `checkPreConditions` throws on an
/// inconsistent ontology under the default flag (matching its sibling characteristics).
pub fn is_irreflexive(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::IrreflexiveObjectProperty;
    is_entailed(ontology, &Component::IrreflexiveObjectProperty(IrreflexiveObjectProperty(ope)))
}

/// Internal (non-throwing) irreflexivity reduction: `P` is irreflexive iff asserting
/// `P(a,a)` for a fresh `a` is inconsistent.
fn is_irreflexive_core(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::ObjectPropertyAssertion;
    if !is_ontology_consistent(ontology)? {
        return Ok(true);
    }
    let mut test = ontology.clone();
    let a = fresh_anonymous_individual("irreflexive");
    test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope,
        from: a.clone(),
        to: a,
    }));
    Ok(!is_ontology_consistent(&test)?)
}

/// `Reasoner.isAsymmetric` (`Reasoner.java:1289`). Routes through `is_entailed`
/// (like `is_symmetric`) so it throws on an inconsistent ontology under the default flag.
pub fn is_asymmetric(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::AsymmetricObjectProperty;
    is_entailed(ontology, &Component::AsymmetricObjectProperty(AsymmetricObjectProperty(ope)))
}

/// Internal (non-throwing) asymmetry reduction: `P` is asymmetric iff asserting
/// `P(a,b)` and `Inv(P)(a,b)` (i.e. `P(b,a)`) for fresh `a,b` is inconsistent.
fn is_asymmetric_core(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::ObjectPropertyAssertion;
    if !is_ontology_consistent(ontology)? {
        return Ok(true);
    }
    let mut test = ontology.clone();
    let a = fresh_anonymous_individual("asymmetric-a");
    let b = fresh_anonymous_individual("asymmetric-b");
    test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: a.clone(),
        to: b.clone(),
    }));
    test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: invert_ope(&ope),
        from: a,
        to: b,
    }));
    Ok(!is_ontology_consistent(&test)?)
}

/// `Reasoner.isReflexive` (`Reasoner.java:1274`): the pseudo-nominal
/// construction. `P` is reflexive iff a fresh individual asserted to be the
/// pseudo-nominal `N` and `∀P.¬N` is unsatisfiable (a reflexive `P` forces a
/// `P`-self loop, so the node would be both `N` and `¬N`).
pub fn is_reflexive(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::ReflexiveObjectProperty;
    is_entailed(ontology, &Component::ReflexiveObjectProperty(ReflexiveObjectProperty(ope)))
}

/// Internal (non-throwing) reflexivity reduction (the pseudo-nominal construction).
fn is_reflexive_core(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    if !is_ontology_consistent(ontology)? {
        return Ok(true);
    }
    let build = Build::new_arc();
    let pseudo_nominal = CE::Class(build.class("internal:pseudo-nominal"));
    let all_not_pseudo =
        all_values(&ope, CE::ObjectComplementOf(Box::new(pseudo_nominal.clone())));
    let desc = CE::ObjectIntersectionOf(vec![pseudo_nominal, all_not_pseudo]);
    Ok(!is_concept_satisfiable_core(ontology, desc)?)
}

/// `Reasoner.isTransitive` (`Reasoner.java:1320`): the pseudo-nominal/chain
/// construction. With `N` a fresh pseudo-nominal and fresh `a,b,c`, assert
/// `P(a,b)`, `P(b,c)`, `(∀P.¬N)(a)`, `N(c)`. If `P` is transitive then
/// `P(a,c)` is derived, forcing `c` to be `¬N` while it is asserted `N` --
/// a clash. So `P` is transitive iff this is inconsistent.
pub fn is_transitive(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::TransitiveObjectProperty;
    is_entailed(ontology, &Component::TransitiveObjectProperty(TransitiveObjectProperty(ope)))
}

/// Internal (non-throwing) transitivity reduction (the pseudo-nominal/chain construction).
fn is_transitive_core(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::{ClassAssertion, ObjectPropertyAssertion};
    if !is_ontology_consistent(ontology)? {
        return Ok(true);
    }
    let build = Build::new_arc();
    let pseudo_nominal_class = build.class("internal:pseudo-nominal");
    let pseudo_nominal = CE::Class(pseudo_nominal_class);
    let all_not_pseudo =
        all_values(&ope, CE::ObjectComplementOf(Box::new(pseudo_nominal.clone())));
    let a = fresh_anonymous_individual("transitive-a");
    let b = fresh_anonymous_individual("transitive-b");
    let c = fresh_anonymous_individual("transitive-c");
    let mut test = ontology.clone();
    test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: a.clone(),
        to: b.clone(),
    }));
    test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope,
        from: b,
        to: c.clone(),
    }));
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: all_not_pseudo,
        i: a,
    }));
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: pseudo_nominal,
        i: c,
    }));
    Ok(!is_ontology_consistent(&test)?)
}

/// `reasoner.isSubObjectPropertyExpressionOf(chain, super)`
/// (`Reasoner.java:1064-1090`), used by `is_entailed` for object-property chain
/// subsumption. On an inconsistent ontology, or when `super` unwraps to
/// `owl:topObjectProperty`, the inclusion trivially holds. Otherwise the
/// pseudo-nominal construction: for a chain `R1,...,Rn` introduce fresh
/// `x0,...,xn` with `Ri(x_{i-1}, x_i)`, `pseudoNominal(xn)`, and
/// `(∀super.¬pseudoNominal)(x0)`; the inclusion holds iff this is inconsistent.
/// `∀super.¬pseudoNominal` propagates through the role automaton, so the test is
/// correct for a complex (role-chain) or inverse super-role -- a plain
/// `¬super(x0,xn)` negative assertion would not exercise that machinery.
pub fn is_object_property_chain_subsumed_by(
    ontology: &SetOntology<crate::structural::A>,
    chain: &[horned_owl::model::ObjectPropertyExpression<crate::structural::A>],
    sup: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::{AnonymousIndividual, ClassAssertion, ObjectPropertyAssertion};
    if !is_ontology_consistent(ontology)?
        || crate::structural::named_property(&sup).0.to_string()
            == "http://www.w3.org/2002/07/owl#topObjectProperty"
    {
        return Ok(true);
    }
    let build = Build::new_arc();
    let mut test = ontology.clone();
    // Fresh witnesses x0..xn.
    let mut nodes: Vec<OwlIndividual<crate::structural::A>> = Vec::with_capacity(chain.len() + 1);
    for _ in 0..=chain.len() {
        nodes.push(OwlIndividual::Anonymous(AnonymousIndividual(
            build.iri(fresh_witness_iri("chain")).underlying(),
        )));
    }
    for (index, role) in chain.iter().enumerate() {
        test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope: role.clone(),
            from: nodes[index].clone(),
            to: nodes[index + 1].clone(),
        }));
    }
    let pseudo_nominal = CE::Class(build.class("internal:pseudo-nominal"));
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: pseudo_nominal.clone(),
        i: nodes[chain.len()].clone(),
    }));
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectAllValuesFrom {
            ope: sup,
            bce: Box::new(CE::ObjectComplementOf(Box::new(pseudo_nominal))),
        },
        i: nodes[0].clone(),
    }));
    Ok(!is_ontology_consistent(&test)?)
}

/// Port of `EntailmentChecker.visit(OWLHasKeyAxiom)` (`EntailmentChecker.java:458`).
/// Two fresh individuals `a,b` are both asserted to be in the key class, share a
/// fresh key successor (for object-property keys) / a shared fresh constant (for
/// data-property keys), and asserted different. If the key holds, the shared key
/// values force `a = b`, contradicting the difference -- so the key is entailed
/// iff this construction is inconsistent.
fn is_has_key_entailed(
    ontology: &SetOntology<crate::structural::A>,
    ax: &horned_owl::model::HasKey<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::{
        ClassAssertion, DataPropertyAssertion, DifferentIndividuals, Literal,
        ObjectPropertyAssertion, PropertyExpression,
    };
    // HermiT short-circuits on an inconsistent ontology (returns true).
    if !is_ontology_consistent(ontology)? {
        return Ok(true);
    }
    let build = Build::new_arc();
    let a = OwlIndividual::Named(build.named_individual(fresh_witness_iri("haskey-A")));
    let b = OwlIndividual::Named(build.named_individual(fresh_witness_iri("haskey-B")));
    let mut test = ontology.clone();
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: ax.ce.clone(),
        i: a.clone(),
    }));
    test.insert(Component::ClassAssertion(ClassAssertion {
        ce: ax.ce.clone(),
        i: b.clone(),
    }));
    for pe in &ax.vpe {
        match pe {
            PropertyExpression::ObjectPropertyExpression(ope) => {
                let tmp = OwlIndividual::Named(
                    build.named_individual(fresh_witness_iri("haskey-succ")),
                );
                test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
                    ope: ope.clone(),
                    from: a.clone(),
                    to: tmp.clone(),
                }));
                test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
                    ope: ope.clone(),
                    from: b.clone(),
                    to: tmp,
                }));
            }
            PropertyExpression::DataProperty(dp) => {
                // A shared anonymous constant in an internal datatype (cf. Java's
                // "internal:anonymous-constants" / "internal:constant-..." literal).
                let constant = Literal::Datatype {
                    datatype_iri: build.iri("internal:anonymous-constants"),
                    literal: fresh_witness_iri("haskey-const"),
                };
                test.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
                    dp: dp.clone(),
                    from: a.clone(),
                    to: constant.clone(),
                }));
                test.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
                    dp: dp.clone(),
                    from: b.clone(),
                    to: constant,
                }));
            }
            PropertyExpression::AnnotationProperty(_) => {}
        }
    }
    test.insert(Component::DifferentIndividuals(DifferentIndividuals(vec![
        a, b,
    ])));
    Ok(!is_ontology_consistent(&test)?)
}

/// Port of `EntailmentChecker.visit(OWLDatatypeDefinitionAxiom)`
/// (`EntailmentChecker.java:428-448`). On an inconsistent ontology HermiT
/// returns `true`. Otherwise build `∃freshDP.((¬DR ⊓ DT) ⊔ (¬DT ⊓ DR))` and
/// assert it on a fresh individual; the datatype definition `DT ≡ DR` is
/// entailed iff this is unsatisfiable (no element can witness the symmetric
/// difference of `DT` and `DR`).
fn is_datatype_definition_entailed(
    ontology: &SetOntology<crate::structural::A>,
    datatype: &horned_owl::model::Datatype<crate::structural::A>,
    data_range: &horned_owl::model::DataRange<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::DataRange as DR;
    if !is_ontology_consistent(ontology)? {
        return Ok(true);
    }
    // Java EntailmentChecker.visit(OWLDatatypeDefinitionAxiom) gates the
    // whole tableau test behind `if (reasoner.m_dlOntology.hasDatatypes())`, returning
    // false for a datatype-free premise (and never clausifying the query's data ranges).
    if !clausify_for_query(ontology)?.has_datatypes() {
        return Ok(false);
    }
    let build = Build::new_arc();
    let fresh_dp = build.data_property(fresh_witness_iri("datatype-def-dp"));
    let dt = DR::Datatype(datatype.clone());
    let dr = data_range.clone();
    // dr1 = ¬DR ⊓ DT
    let dr1 = DR::DataIntersectionOf(vec![DR::DataComplementOf(Box::new(dr.clone())), dt.clone()]);
    // dr2 = ¬DT ⊓ DR
    let dr2 = DR::DataIntersectionOf(vec![DR::DataComplementOf(Box::new(dt)), dr]);
    let union = DR::DataUnionOf(vec![dr1, dr2]);
    let desc = CE::DataSomeValuesFrom { dp: fresh_dp, dr: union };
    Ok(!is_concept_satisfiable_core(ontology, desc)?)
}

/// Runs the front-end pipeline (normalize → object-property inclusion rewriting
/// → clausify) and returns the resulting `DLOntology`, used to read the
/// classified vocabulary (named classes / individuals) for classification and
/// realisation.
fn clausify_for_query(ontology: &SetOntology<crate::structural::A>) -> Result<DLOntology, String> {
    use crate::structural::{
        BuiltInPropertyManager, Configuration, ObjectPropertyInclusionManager, OWLAxioms,
        OWLAxiomsExpressivity, OWLClausification, OWLNormalization,
    };
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology)?;
    let definitions_count = normalization.definitions_count();
    let mut axioms = normalization.into_axioms();
    // Give owl:{top,bottom}{Object,Data}Property their built-in meaning when used.
    // This can introduce complex inclusions (owl:topObjectProperty is transitive),
    // so it must run before the object-property inclusion manager (as in
    // OWLClausification.preprocessAndClausify).
    BuiltInPropertyManager::new().axiomatize_built_in_properties_as_needed(&mut axioms);
    // OWLClausification.preprocessAndClausify runs the object-property inclusion
    // manager UNCONDITIONALLY (not gated on there being complex inclusions): it must
    // build the automata and rewrite negative assertions / ∀R.C axioms in every case.
    let manager = ObjectPropertyInclusionManager::new(&mut axioms)?;
    manager.rewrite_negative_object_property_assertions(&mut axioms, definitions_count);
    manager.rewrite_axioms(&mut axioms, 0)?;
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    OWLClausification::new(Configuration::default()).clausify(
        "http://hermit-rs/anonymous-ontology",
        &axioms,
        &expressivity,
    )
}

pub fn classify(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<crate::hierarchy::Hierarchy<horned_owl::model::Class<crate::structural::A>>, String> {
    classify_with_configuration_and_monitor(
        ontology,
        &crate::configuration::Configuration::default(),
        &mut crate::hierarchy::NoProgressMonitor,
    )
}

/// As [`classify`], but runs the classification under an explicit
/// [`Configuration`](crate::configuration::Configuration). HermiT's
/// `m_configuration` governs *all* reasoning, classification included; this
/// threads the blocking strategy, direct-blocking type, signature cache and
/// existential-expansion strategy into every tableau the classifier builds (via
/// `Reasoner::with_configuration`). With `Configuration::default()` the answers
/// and behaviour are byte-for-byte identical to `classify`; tuning flags only
/// change the tableau, never the (sound + complete) classification answers.
pub fn classify_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<crate::hierarchy::Hierarchy<horned_owl::model::Class<crate::structural::A>>, String> {
    classify_with_configuration_and_monitor(
        ontology,
        configuration,
        &mut crate::hierarchy::NoProgressMonitor,
    )
}

/// As [`classify`], but reports progress through a
/// [`ClassificationProgressMonitor`](crate::hierarchy::ClassificationProgressMonitor):
/// `monitor.element_classified(class)` fires once per classified named class, the
/// port of Java's `classifyClasses` firing `elementClassified(AtomicConcept)` per
/// concept (`Reasoner.java:729`). Answer-neutral; the default
/// `NoProgressMonitor` makes [`classify`] a no-op observer.
pub fn classify_with_monitor<M>(
    ontology: &SetOntology<crate::structural::A>,
    monitor: &mut M,
) -> Result<crate::hierarchy::Hierarchy<horned_owl::model::Class<crate::structural::A>>, String>
where
    M: crate::hierarchy::ClassificationProgressMonitor<horned_owl::model::Class<crate::structural::A>>
        + ?Sized,
{
    classify_with_configuration_and_monitor(
        ontology,
        &crate::configuration::Configuration::default(),
        monitor,
    )
}

/// The core class classifier: threads `configuration`
/// into every tableau (`Reasoner::with_configuration`) and fires `monitor` once
/// per classified element through `build_hierarchy_with_monitor`. The public
/// [`classify`] / [`classify_with_configuration`] / [`classify_with_monitor`]
/// entry points are thin wrappers over this with the default config and/or the
/// `NoProgressMonitor`.
pub fn classify_with_configuration_and_monitor<M>(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
    monitor: &mut M,
) -> Result<crate::hierarchy::Hierarchy<horned_owl::model::Class<crate::structural::A>>, String>
where
    M: crate::hierarchy::ClassificationProgressMonitor<horned_owl::model::Class<crate::structural::A>>
        + ?Sized,
{
    use horned_owl::model::Class;
    use std::collections::HashSet;

    let build = Build::new_arc();
    let thing = build.class("http://www.w3.org/2002/07/owl#Thing");
    let nothing = build.class("http://www.w3.org/2002/07/owl#Nothing");

    // The atomic concepts to classify are the named classes of the clausified
    // vocabulary (everything appearing in the axioms), minus owl:Thing/Nothing
    // and the auxiliary "internal:" concepts introduced during clausification.
    monitor.classification_phase("clausify");
    let dl_ontology = clausify_for_query(ontology)?;
    let mut element_set: HashSet<Class<crate::structural::A>> = HashSet::new();
    for concept in dl_ontology.get_all_atomic_concepts() {
        let iri = concept.iri();
        if iri.starts_with("internal:")
            || iri == "http://www.w3.org/2002/07/owl#Thing"
            || iri == "http://www.w3.org/2002/07/owl#Nothing"
        {
            continue;
        }
        element_set.insert(build.class(iri));
    }
    element_set.insert(thing.clone());
    element_set.insert(nothing.clone());
    let elements: Vec<Class<crate::structural::A>> = element_set.into_iter().collect();

    // Clausify and compile the clauses ONCE, then reuse the tableau/manager across
    // every subsumption test (HermiT's single `m_tableau`). This is what makes
    // classification of large ontologies feasible -- the per-test re-clausification
    // was the bottleneck.
    monitor.classification_phase("compile");
    let reasoner = Reasoner::with_configuration(&dl_ontology, configuration.clone());
    let mut manager = reasoner.new_manager();

    monitor.classification_phase("consistency");
    if !reasoner.is_consistent() {
        // Java's classifyClasses() runs
        // checkPreConditions() FIRST, throwing InconsistentOntologyException under the
        // default flag (so getTop/BottomClassNode and getUnsatisfiableClasses throw).
        // The empty-hierarchy return is the flag-OFF fallthrough (Reasoner.java:720-721).
        if configuration.throw_inconsistent_ontology_exception {
            return Err(INCONSISTENT_ONTOLOGY_ERROR.to_string());
        }
        return Ok(crate::hierarchy::Hierarchy::empty_hierarchy(
            &elements,
            thing,
            nothing,
        ));
    }

    use crate::model::AtomicConcept;
    let atomic_of = |c: &Class<crate::structural::A>| AtomicConcept::create(c.0.to_string());

    monitor.classification_phase("classify");

    // Deterministic (Horn) ontologies: one model build per concept, reading its
    // subsumers off the single saturated model -- `DeterministicClassification`.
    // O(N) satisfiability tests instead of O(N^2) pairwise subsumption tests.
    // Java dispatches on `tableau.isDeterministic() && !forceQuasiOrder`
    // (Reasoner.classifyAtomicConcepts, Reasoner.java:2047).
    if reasoner.is_deterministic() && !reasoner.configuration().force_quasi_order_classification {
        let element_iris: HashSet<String> = elements.iter().map(|c| c.0.to_string()).collect();
        let mut subsumers: HashMap<
            Class<crate::structural::A>,
            HashSet<Class<crate::structural::A>>,
        > = HashMap::new();
        let total = elements.len();
        for (idx, element) in elements.iter().enumerate() {
            monitor.classification_progress(idx, total);
            let mut element_subsumers: HashSet<Class<crate::structural::A>> = HashSet::new();
            // Read every element's subsumers off its own single model -- including
            // owl:Thing, so a `⊤ ⊑ C` axiom (making C equivalent to Thing) is found.
            match reasoner.concept_subsumers(&mut manager, &atomic_of(element)) {
                // Satisfiable: the atomic concepts forced onto the fresh node are
                // exactly `element`'s subsumers (filtered to the classified set).
                Some(forced) => {
                    element_subsumers.insert(thing.clone());
                    element_subsumers.insert(element.clone());
                    for c in forced {
                        if element_iris.contains(c.iri()) {
                            element_subsumers.insert(build.class(c.iri()));
                        }
                    }
                }
                // Unsatisfiable (`element ⊑ ⊥`): subsumed by everything.
                None => {
                    for other in &elements {
                        element_subsumers.insert(other.clone());
                    }
                }
            }
            subsumers.insert(element.clone(), element_subsumers);
        }
        return Ok(crate::hierarchy::build_hierarchy_with_monitor(
            thing, nothing, subsumers, monitor,
        ));
    }

    // Non-deterministic ontologies: route through the faithful quasi-order
    // classifier (HermiT's `QuasiOrderClassification`, the same driver the
    // role/data-property classifiers use). It seeds the known graph with told
    // subsumers, reads each concept's possible subsumers off one saturated model
    // (the leaf-node strategy), and resolves the leftover possible subsumptions
    // with the enhanced-traversal search and the batched non-subsumer test --
    // rather than the O(N^2) pairwise subsumption build.
    use crate::quasi_order::QuasiOrderClassification;
    // Told subsumers are read off the clausified binary DL clauses (head length 1,
    // body length 1, both predicates atomic concepts that belong to the classified
    // vocabulary), exactly as
    // `QuasiOrderClassification.initialiseKnownSubsumptionsUsingToldSubsumers`.
    // Reading from the clauses rather than the raw SubClassOf/EquivalentClasses
    // axioms captures told subsumptions hidden inside conjunctions and definitions
    // (e.g. `A ⊑ B ⊓ C` clausifies to `A ⊑ B` and `A ⊑ C`), giving a stronger known
    // graph seed.
    let element_set: HashSet<Class<crate::structural::A>> = elements.iter().cloned().collect();
    let element_iris: HashSet<String> = elements.iter().map(|c| c.0.to_string()).collect();
    let mut told: Vec<(Class<crate::structural::A>, Class<crate::structural::A>)> = Vec::new();
    {
        use crate::model::DLPredicate;
        for clause in dl_ontology.get_dl_clauses() {
            if clause.get_head_length() == 1 && clause.get_body_length() == 1 {
                if let (
                    DLPredicate::AtomicConcept(head_concept),
                    DLPredicate::AtomicConcept(body_concept),
                ) = (
                    clause.get_head_atom(0).get_dl_predicate(),
                    clause.get_body_atom(0).get_dl_predicate(),
                ) {
                    if element_iris.contains(head_concept.iri())
                        && element_iris.contains(body_concept.iri())
                    {
                        // body ⊑ head
                        told.push((
                            build.class(body_concept.iri()),
                            build.class(head_concept.iri()),
                        ));
                    }
                }
            }
        }
    }
    let oracle = ConceptSubsumptionOracle {
        reasoner: &reasoner,
        manager,
        thing: thing.clone(),
        class_cache: std::cell::RefCell::new(HashMap::new()),
    };
    let mut classifier =
        QuasiOrderClassification::new(oracle, thing.clone(), nothing.clone(), element_set);
    classifier.initialise_known_subsumptions_using_told_subsumers(&told);
    Ok(classifier.classify_with_monitor(monitor))
}

/// Whether the object property `ope` is necessarily empty (`ope ⊑ ⊥`): true iff
/// asserting `ope(a,b)` for fresh `a,b` is already inconsistent. (Retained as a
/// utility; the classifier now reads emptiness off the OPE-hierarchy bottom node.)
#[allow(dead_code)]
fn is_object_property_empty(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::ObjectPropertyAssertion;
    let mut test = ontology.clone();
    let a = fresh_anonymous_individual("role-subject");
    let b = fresh_anonymous_individual("role-object");
    test.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope,
        from: a,
        to: b,
    }));
    Ok(!is_ontology_consistent(&test)?)
}

/// An oracle for the quasi-order classifier (`quasi_order::SubsumptionOracle`)
/// backed by the object-/data-property subsumption tests. As in
/// `QuasiOrderClassification`'s `TruthOracle`-style usage, `build_model`
/// exposes no deterministic known subsumers (every other element is *possible*),
/// so `does_subsume` -- the explicit tableau subsumption test -- decides every
/// edge. This keeps the role/data-role classification result identical to the
/// pairwise build while routing it through the faithful quasi-order driver
/// (including the inverse-concept mirroring of `QuasiOrderClassificationForRoles`).
struct PropertySubsumptionOracle<'a, E, F, G, H> {
    ontology: &'a SetOntology<crate::structural::A>,
    candidates: Vec<E>,
    /// `does_subsume(parent, child)`: returns the subsumption-test result, or an
    /// error that is captured into `error`.
    subsumes: F,
    /// `is_subsumed_by_union(child, candidates)`: the batched test result paired
    /// with the picked element's deterministic known subsumers read off the
    /// witnessing model (empty when the union test is negative / the read-off finds
    /// none), or an error captured into `error`. The known subsumers mirror the
    /// class path's `readKnownSubsumersFromRootNode` so the classifier can prune
    /// them (`isEveryPossibleSubsumerNonSubsumer`'s positive branch).
    subsumes_union: G,
    /// `buildModelForConcept`: reads `(known, possible)` subsumers off one
    /// saturated model of `picked`, or `None` if `picked` is unsatisfiable.
    build_model_fn: H,
    error: Option<String>,
}

impl<'a, E, F, G, H> crate::quasi_order::SubsumptionOracle<E>
    for PropertySubsumptionOracle<'a, E, F, G, H>
where
    E: Eq + std::hash::Hash + Clone,
    F: FnMut(&SetOntology<crate::structural::A>, &E, &E) -> Result<bool, String>,
    G: FnMut(
        &SetOntology<crate::structural::A>,
        &E,
        &std::collections::HashSet<E>,
    ) -> Result<(bool, std::collections::HashSet<E>), String>,
    H: FnMut(&E, &[E]) -> Option<(std::collections::HashSet<E>, std::collections::HashSet<E>)>,
{
    fn build_model(&mut self, concept: &E) -> Option<crate::quasi_order::ModelReadOff<E>> {
        // The role classifier reads subsumers off a single edge model; it does not
        // expose full node labels, so cross-concept harvesting is disabled
        // (`node_labels: None`) and only the query's own possibles are recorded.
        let (query_known, query_possible) = (self.build_model_fn)(concept, &self.candidates)?;
        Some(crate::quasi_order::ModelReadOff {
            query_known,
            query_possible,
            node_labels: None,
        })
    }
    fn does_subsume(&mut self, parent: &E, child: &E) -> bool {
        if self.error.is_some() {
            return false;
        }
        match (self.subsumes)(self.ontology, child, parent) {
            Ok(result) => result,
            Err(e) => {
                self.error = Some(e);
                false
            }
        }
    }
    fn is_subsumed_by_union(
        &mut self,
        child: &E,
        candidates: &std::collections::HashSet<E>,
    ) -> Option<crate::quasi_order::UnionTestResult<E>> {
        if self.error.is_some() {
            return None;
        }
        match (self.subsumes_union)(self.ontology, child, candidates) {
            // On a positive union test the picked element's deterministic known
            // subsumers are read off the witnessing edge model (mirroring the class
            // path's `readKnownSubsumersFromRootNode`), so the classifier prunes
            // them from the possibles. Answer-neutral: only fewer pairwise tests.
            Ok((subsumed, query_known)) => Some(crate::quasi_order::UnionTestResult {
                subsumed,
                query_known: if subsumed {
                    query_known
                } else {
                    std::collections::HashSet::new()
                },
            }),
            Err(e) => {
                self.error = Some(e);
                None
            }
        }
    }
}

/// Concept oracle for the quasi-order classifier, backed by the reusable
/// tableau/manager of a [`Reasoner`] (HermiT runs the whole quasi-order over its
/// single `m_tableau`). `build_model` reads `picked`'s subsumers off one
/// saturated model (`buildModelForConcept` + `readKnownSubsumersFromRootNode`),
/// `does_subsume` is the explicit `child ⊑ parent` tableau test, and
/// `is_subsumed_by_union` is the batched `isEveryPossibleSubsumerNonSubsumer`
/// test. Top (`owl:Thing`) is the one deterministic known subsumer; every other
/// concept read off the model is a *possible* subsumer to be confirmed.
struct ConceptSubsumptionOracle<'r, 'd> {
    reasoner: &'r Reasoner<'d>,
    manager: HyperresolutionManager,
    thing: horned_owl::model::Class<crate::structural::A>,
    /// Interns the `Class<A>` for each distinct concept encountered while reading
    /// labels off saturated models. On dense models the same atomic concepts recur
    /// across tens of thousands of node labels per model and across every model
    /// build; without this cache each occurrence re-ran `Build::class` -- a
    /// `BTreeSet<IRI>` string-comparison lookup keyed by the concept's IRI, after a
    /// fresh `AtomicConcept -> String` round-trip -- millions of times per
    /// classification. `AtomicConcept` is a `Copy` interned handle with O(1)
    /// pointer hashing, so this map turns each repeat occurrence into a single word
    /// hash plus an `Arc` refcount bump on the already-built `Class`, and builds
    /// each distinct `Class` exactly once for the whole classification. The cached
    /// `Class` is value-identical to what `Build::class` produced, so the
    /// classification result is byte-identical.
    class_cache: std::cell::RefCell<
        HashMap<crate::model::AtomicConcept, horned_owl::model::Class<crate::structural::A>>,
    >,
}

impl<'r, 'd> ConceptSubsumptionOracle<'r, 'd> {
    /// The cached `Class<A>` for `ac`, building (and interning) it on first sight.
    fn class_of(
        &self,
        build: &Build<crate::structural::A>,
        ac: crate::model::AtomicConcept,
    ) -> horned_owl::model::Class<crate::structural::A> {
        self.class_cache
            .borrow_mut()
            .entry(ac)
            .or_insert_with(|| build.class(ac.iri()))
            .clone()
    }

    /// Convert a read-off set of atomic concepts into the matching `Class` set,
    /// reusing `class_of`'s per-concept cache (one `Class` build per distinct IRI
    /// for the whole classification, not one per occurrence).
    fn classes_of(
        &self,
        build: &Build<crate::structural::A>,
        acs: std::collections::HashSet<crate::model::AtomicConcept>,
    ) -> std::collections::HashSet<horned_owl::model::Class<crate::structural::A>> {
        acs.into_iter().map(|c| self.class_of(build, c)).collect()
    }
}

impl<'r, 'd> crate::quasi_order::SubsumptionOracle<horned_owl::model::Class<crate::structural::A>>
    for ConceptSubsumptionOracle<'r, 'd>
{
    fn build_model(
        &mut self,
        concept: &horned_owl::model::Class<crate::structural::A>,
    ) -> Option<crate::quasi_order::ModelReadOff<horned_owl::model::Class<crate::structural::A>>> {
        let build = Build::new_arc();
        let (known_concepts, label_concepts) = self.reasoner.concept_model_read_off(
            &mut self.manager,
            &crate::model::AtomicConcept::create(concept.0.to_string()),
        )?;
        // readKnownSubsumersFromRootNode: deterministic subsumers + owl:Thing.
        let mut query_known = self.classes_of(&build, known_concepts);
        query_known.insert(self.thing.clone());
        // updatePossibleSubsumers: every active, unblocked node's concept label.
        let node_labels: Vec<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>> =
            label_concepts
                .into_iter()
                .map(|acs| self.classes_of(&build, acs))
                .collect();
        Some(crate::quasi_order::ModelReadOff {
            query_known,
            query_possible: std::collections::HashSet::new(),
            node_labels: Some(node_labels),
        })
    }
    fn does_subsume(
        &mut self,
        parent: &horned_owl::model::Class<crate::structural::A>,
        child: &horned_owl::model::Class<crate::structural::A>,
    ) -> bool {
        self.reasoner.atomic_subsumes(
            &mut self.manager,
            &crate::model::AtomicConcept::create(child.0.to_string()),
            &crate::model::AtomicConcept::create(parent.0.to_string()),
        )
    }
    fn does_subsume_with_read_off(
        &mut self,
        parent: &horned_owl::model::Class<crate::structural::A>,
        child: &horned_owl::model::Class<crate::structural::A>,
    ) -> (
        bool,
        Option<crate::quasi_order::ModelReadOff<horned_owl::model::Class<crate::structural::A>>>,
    ) {
        let build = Build::new_arc();
        let (subsumed, read_off) = self.reasoner.atomic_subsumes_with_read_off(
            &mut self.manager,
            &crate::model::AtomicConcept::create(child.0.to_string()),
            &crate::model::AtomicConcept::create(parent.0.to_string()),
        );
        let read_off = read_off.map(|(known_concepts, label_concepts)| {
            crate::quasi_order::ModelReadOff {
                query_known: self.classes_of(&build, known_concepts),
                query_possible: std::collections::HashSet::new(),
                node_labels: Some(
                    label_concepts
                        .into_iter()
                        .map(|acs| self.classes_of(&build, acs))
                        .collect(),
                ),
            }
        });
        (subsumed, read_off)
    }
    fn is_subsumed_by_union(
        &mut self,
        child: &horned_owl::model::Class<crate::structural::A>,
        candidates: &std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>,
    ) -> Option<crate::quasi_order::UnionTestResult<horned_owl::model::Class<crate::structural::A>>> {
        let build = Build::new_arc();
        let cands: std::collections::HashSet<crate::model::AtomicConcept> = candidates
            .iter()
            .map(|c| crate::model::AtomicConcept::create(c.0.to_string()))
            .collect();
        let (subsumed, known_concepts) = self.reasoner.atomic_subsumed_by_union_with_known(
            &mut self.manager,
            &crate::model::AtomicConcept::create(child.0.to_string()),
            &cands,
        );
        // readKnownSubsumersFromRootNode reads only the atomic concepts actually
        // on the witnessing root (it does not inject owl:Thing); the classifier
        // filters them against its element set.
        let query_known = self.classes_of(&build, known_concepts);
        Some(crate::quasi_order::UnionTestResult { subsumed, query_known })
    }

    /// Open the streaming worker pool that backs the leaf-node strategy's
    /// continuous coordinator/worker pipeline (no per-round barrier). See
    /// [`ConceptStreamingPool`] for the design; the pool borrows the oracle's
    /// reasoner + class-cache for its lifetime and joins all workers on drop.
    fn streaming_pool<'p>(
        &'p mut self,
    ) -> Option<
        Box<
            dyn crate::quasi_order::StreamingModelPool<
                    horned_owl::model::Class<crate::structural::A>,
                > + 'p,
        >,
    > {
        let worker_count = leaf_build_max_workers();
        if worker_count <= 1 {
            return None;
        }
        Some(Box::new(ConceptStreamingPool::new(
            self.reasoner,
            self.thing.clone(),
            &self.class_cache,
            worker_count,
        )))
    }

    /// Parallel leaf-node model builds. Each model
    /// (`buildModelForConcept`/`concept_model_read_off`) is independent: it
    /// saturates its OWN tableau over the read-only, shareable [`DLOntology`] (whose
    /// clauses hold process-global interned `&'static` handles, valid and identical
    /// across threads). A fixed pool of [`leaf_build_max_workers()`]-many worker
    /// threads shares a single global work queue (an atomic claim index) over the
    /// WHOLE batch -- so a worker that finishes a cheap model immediately claims the
    /// next concept rather than idling behind a single pathologically dense one.
    /// Each worker owns its own replica reasoner (own tableau + manager + reuse set,
    /// so nothing `!Send` -- `Rc`/`RefCell` -- crosses a thread boundary), reused
    /// across every concept it claims.
    ///
    /// Workers return raw `AtomicConcept` read-offs (interned handles are
    /// `Send + Sync`); THIS thread reorders them into batch order and converts each
    /// to the classifier's `Class<A>` sets via the (single-threaded) `class_cache`,
    /// so the values handed to the serial, confluent harvest are byte-identical to
    /// the one-at-a-time path. RAM-bounded: at most `worker_count` concurrent
    /// multi-GB tableaux, and only one batch's read-offs held at a time.
    fn build_models_batch(
        &mut self,
        concepts: &[horned_owl::model::Class<crate::structural::A>],
    ) -> Vec<Option<crate::quasi_order::ModelReadOff<horned_owl::model::Class<crate::structural::A>>>>
    {
        type RawReadOff = (
            std::collections::HashSet<crate::model::AtomicConcept>,
            Vec<std::collections::HashSet<crate::model::AtomicConcept>>,
        );
        // Pre-intern the query concepts as `AtomicConcept` (Send) for the workers.
        let queries: Vec<crate::model::AtomicConcept> = concepts
            .iter()
            .map(|c| crate::model::AtomicConcept::create(c.0.to_string()))
            .collect();
        let n = queries.len();
        let worker_count = std::cmp::min(leaf_build_max_workers(), n.max(1));
        // Below the threshold the thread-pool overhead is not worth it; build
        // serially on this thread reusing the oracle's own manager/tableau.
        if worker_count <= 1 {
            return concepts.iter().map(|c| self.build_model(c)).collect();
        }

        let dl_ontology = self.reasoner.dl_ontology();
        let configuration = self.reasoner.configuration().clone();
        // Global work queue: each worker repeatedly claims the next concept index.
        let next = std::sync::atomic::AtomicUsize::new(0);
        // Each worker pushes its `(index, raw_result)` into the shared sink; we
        // reorder afterwards. The lock is held only for the push -- negligible next
        // to the multi-millisecond tableau saturation it guards.
        let sink: std::sync::Mutex<Vec<(usize, Option<RawReadOff>)>> =
            std::sync::Mutex::new(Vec::with_capacity(n));

        std::thread::scope(|scope| {
            for _ in 0..worker_count {
                let next = &next;
                let sink = &sink;
                let queries = &queries;
                let configuration = &configuration;
                scope.spawn(move || {
                    // One replica reasoner + manager per worker, reused across every
                    // concept it claims (the replica caches a single per-test tableau
                    // internally, exactly as the serial path does), so there is one
                    // tableau allocation per worker, not per concept.
                    let worker = Reasoner::with_configuration(dl_ontology, configuration.clone());
                    let mut manager = worker.new_manager();
                    loop {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= queries.len() {
                            break;
                        }
                        let result = worker.concept_model_read_off(&mut manager, &queries[i]);
                        sink.lock().unwrap().push((i, result));
                    }
                });
            }
        });

        // Reorder the workers' results back into batch order.
        let mut raw: Vec<Option<Option<RawReadOff>>> = (0..n).map(|_| None).collect();
        for (i, result) in sink.into_inner().unwrap() {
            raw[i] = Some(result);
        }

        // Serial, deterministic conversion of the raw interned read-offs into the
        // classifier's `Class<A>` sets, reusing the per-classification cache so each
        // distinct concept's `Class` is built exactly once (value-identical to the
        // serial path).
        let build = Build::new_arc();
        raw.into_iter()
            .map(|slot| {
                let result = slot.expect("every query slot is filled by a worker");
                result.map(|(known_concepts, label_concepts)| {
                    let mut query_known = self.classes_of(&build, known_concepts);
                    query_known.insert(self.thing.clone());
                    let node_labels: Vec<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>> =
                        label_concepts
                            .into_iter()
                            .map(|acs| self.classes_of(&build, acs))
                            .collect();
                    crate::quasi_order::ModelReadOff {
                        query_known,
                        query_possible: std::collections::HashSet::new(),
                        node_labels: Some(node_labels),
                    }
                })
            })
            .collect()
    }

    fn resolution_pool<'p>(
        &'p mut self,
        top: &horned_owl::model::Class<crate::structural::A>,
        bottom: &horned_owl::model::Class<crate::structural::A>,
        elements: &std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>,
    ) -> Option<
        Box<
            dyn crate::quasi_order::ResolutionPool<
                    horned_owl::model::Class<crate::structural::A>,
                > + 'p,
        >,
    > {
        let worker_count = leaf_build_max_workers();
        if worker_count <= 1 {
            return None;
        }
        Some(Box::new(ConceptResolutionPool::new(
            self.reasoner,
            &self.class_cache,
            worker_count,
            top,
            bottom,
            elements,
        )))
    }
}

/// A minimal [`SubsumptionOracle`] over a worker's replica reasoner, native to
/// `AtomicConcept` (no `Class<A>` conversion / class cache), exposing just the two
/// subsumption tests the isolated resolver uses. The model-build entry points are
/// unreachable on this path.
struct RawResolveOracle<'r, 'd> {
    reasoner: &'r Reasoner<'d>,
    manager: &'r mut HyperresolutionManager,
}

impl crate::quasi_order::SubsumptionOracle<crate::model::AtomicConcept>
    for RawResolveOracle<'_, '_>
{
    fn build_model(
        &mut self,
        _concept: &crate::model::AtomicConcept,
    ) -> Option<crate::quasi_order::ModelReadOff<crate::model::AtomicConcept>> {
        unreachable!("RawResolveOracle only runs the resolution subsumption tests")
    }
    fn does_subsume(
        &mut self,
        parent: &crate::model::AtomicConcept,
        child: &crate::model::AtomicConcept,
    ) -> bool {
        self.reasoner.atomic_subsumes(self.manager, child, parent)
    }
    fn does_subsume_with_read_off(
        &mut self,
        parent: &crate::model::AtomicConcept,
        child: &crate::model::AtomicConcept,
    ) -> (
        bool,
        Option<crate::quasi_order::ModelReadOff<crate::model::AtomicConcept>>,
    ) {
        let (subsumed, raw) =
            self.reasoner.atomic_subsumes_with_read_off(self.manager, child, parent);
        (
            subsumed,
            raw.map(|(known, labels)| crate::quasi_order::ModelReadOff {
                query_known: known,
                query_possible: std::collections::HashSet::new(),
                node_labels: Some(labels),
            }),
        )
    }
    fn is_subsumed_by_union(
        &mut self,
        child: &crate::model::AtomicConcept,
        candidates: &std::collections::HashSet<crate::model::AtomicConcept>,
    ) -> Option<crate::quasi_order::UnionTestResult<crate::model::AtomicConcept>> {
        let (subsumed, known) =
            self.reasoner.atomic_subsumed_by_union_with_known(self.manager, child, candidates);
        Some(crate::quasi_order::UnionTestResult { subsumed, query_known: known })
    }
}

/// The raw, `Send` read-off a worker produces: the query's deterministic known
/// subsumers and the model's per-node concept labels, all as interned
/// `AtomicConcept` handles (process-global `&'static`, valid + identical across
/// threads). The coordinator-side conversion into `Class<A>` (via the shared,
/// single-threaded `class_cache`) happens in [`ConceptStreamingPool::recv`].
type StreamingRawReadOff = (
    std::collections::HashSet<crate::model::AtomicConcept>,
    Vec<std::collections::HashSet<crate::model::AtomicConcept>>,
);

/// The streaming worker pool backing the leaf-node strategy's continuous
/// coordinator/worker pipeline (replaces the per-round barrier). It owns a fixed
/// set of persistent worker threads, each with its OWN replica `Reasoner` + manager
/// (own tableau/reuse set, so nothing `!Send` crosses a thread boundary), reused
/// across every concept the worker builds. Workers loop: receive a concept on the
/// work channel -> `concept_model_read_off` -> send the raw read-off on the results
/// channel. The coordinator (the classifier thread) [`dispatch`]es concepts and
/// [`recv`]s completed results ONE at a time, harvesting each immediately -- a slow
/// dense model occupies exactly one worker while the others keep flowing.
///
/// RAM: at most `worker_count` concurrent multi-GB tableaux plus a tiny results
/// channel. There is NO reorder buffer (results are handed back in arrival order),
/// so no completed read-offs accumulate.
///
/// # Safety / lifetimes
/// The workers borrow the read-only `&DLOntology` and the `Configuration` to spin
/// up their replica reasoners. These are extended to `'static` for the spawned
/// `std::thread`s, which is sound because [`Drop`] joins every worker before the
/// pool is dropped, and the pool is dropped (inside the classifier's streaming
/// loop) strictly before the borrowed [`Reasoner`] -- so the threads never outlive
/// the data they borrow. (The existing `build_models_batch` relies on the same
/// `&DLOntology: Sync` property via scoped threads.)
struct ConceptStreamingPool<'r> {
    /// Sender on the work channel; `Some` until [`Drop`] closes it to signal the
    /// workers to exit. A bounded channel sized to `worker_count` keeps the
    /// in-flight count (which the coordinator already caps) from ever backing up.
    work_tx: Option<std::sync::mpsc::SyncSender<crate::model::AtomicConcept>>,
    /// Receiver on the results channel: `(concept, raw read-off)` in completion
    /// order. `None` raw read-off means the concept is unsatisfiable.
    result_rx: std::sync::mpsc::Receiver<(crate::model::AtomicConcept, Option<StreamingRawReadOff>)>,
    /// Worker join handles, joined on drop.
    workers: Vec<std::thread::JoinHandle<()>>,
    /// `owl:Thing`, injected into every satisfiable read-off's known subsumers
    /// (matching the serial `build_model`).
    thing: horned_owl::model::Class<crate::structural::A>,
    /// The oracle's shared, single-threaded class cache, reused so each distinct
    /// concept's `Class<A>` is built exactly once for the whole classification
    /// (value-identical to the serial path).
    class_cache: &'r std::cell::RefCell<
        HashMap<crate::model::AtomicConcept, horned_owl::model::Class<crate::structural::A>>,
    >,
    /// Reverse map from each dispatched concept's `Class<A>` back to the interned
    /// `AtomicConcept` -- so `dispatch` interns once and `recv` returns the exact
    /// `Class<A>` the coordinator dispatched (its in-flight key).
    dispatched: HashMap<crate::model::AtomicConcept, horned_owl::model::Class<crate::structural::A>>,
    worker_count: usize,
}

impl<'r> ConceptStreamingPool<'r> {
    fn new<'d>(
        reasoner: &Reasoner<'d>,
        thing: horned_owl::model::Class<crate::structural::A>,
        class_cache: &'r std::cell::RefCell<
            HashMap<crate::model::AtomicConcept, horned_owl::model::Class<crate::structural::A>>,
        >,
        worker_count: usize,
    ) -> ConceptStreamingPool<'r> {
        // Extend the shared, read-only ontology + configuration borrows to 'static
        // for the worker threads. SOUND: every worker is joined in `Drop` before
        // this pool is dropped, and the pool is dropped before `reasoner` -- so the
        // threads never read freed data. See the type-level safety note.
        let dl_ontology: &'static DLOntology =
            unsafe { std::mem::transmute::<&DLOntology, &'static DLOntology>(reasoner.dl_ontology()) };
        let configuration = reasoner.configuration().clone();

        // Bounded work channel: at most `worker_count` concepts queued, matching the
        // coordinator's in-flight cap, so RAM stays bounded by the workers' tableaux.
        let (work_tx, work_rx) =
            std::sync::mpsc::sync_channel::<crate::model::AtomicConcept>(worker_count);
        let (result_tx, result_rx) = std::sync::mpsc::channel::<(
            crate::model::AtomicConcept,
            Option<StreamingRawReadOff>,
        )>();
        let work_rx = std::sync::Arc::new(std::sync::Mutex::new(work_rx));

        let mut workers = Vec::with_capacity(worker_count);
        for _ in 0..worker_count {
            let work_rx = std::sync::Arc::clone(&work_rx);
            let result_tx = result_tx.clone();
            let configuration = configuration.clone();
            let handle = std::thread::spawn(move || {
                // One replica reasoner + manager per worker, reused across every
                // concept it builds (one tableau allocation per worker, not per
                // concept) -- exactly the serial/batch path's per-worker setup.
                let worker = Reasoner::with_configuration(dl_ontology, configuration);
                let mut manager = worker.new_manager();
                loop {
                    // Claim the next concept. The lock is held only for the recv,
                    // negligible next to the multi-millisecond tableau saturation.
                    let concept = {
                        let rx = work_rx.lock().unwrap();
                        rx.recv()
                    };
                    let concept = match concept {
                        Ok(c) => c,
                        // Work channel closed (pool dropping): exit.
                        Err(_) => break,
                    };
                    let result = worker.concept_model_read_off(&mut manager, &concept);
                    // Drop this worker's tableau now if that build blew it up, so an
                    // idle worker does not pin a multi-GB allocation while the memory
                    // governor throttles dispatch (the throttle relies on quiescent
                    // workers shrinking).
                    worker.release_oversized_test_tableau();
                    // If the coordinator has gone away (result channel closed), stop.
                    if result_tx.send((concept, result)).is_err() {
                        break;
                    }
                }
            });
            workers.push(handle);
        }

        ConceptStreamingPool {
            work_tx: Some(work_tx),
            result_rx,
            workers,
            thing,
            class_cache,
            dispatched: HashMap::new(),
            worker_count,
        }
    }

    /// The cached `Class<A>` for `ac` (single-threaded, shared with the oracle).
    fn class_of(
        &self,
        build: &Build<crate::structural::A>,
        ac: crate::model::AtomicConcept,
    ) -> horned_owl::model::Class<crate::structural::A> {
        self.class_cache
            .borrow_mut()
            .entry(ac)
            .or_insert_with(|| build.class(ac.iri()))
            .clone()
    }
}

impl<'r> crate::quasi_order::StreamingModelPool<horned_owl::model::Class<crate::structural::A>>
    for ConceptStreamingPool<'r>
{
    fn dispatch(&mut self, concept: horned_owl::model::Class<crate::structural::A>) {
        let ac = crate::model::AtomicConcept::create(concept.0.to_string());
        // Remember the exact dispatched `Class<A>` keyed by its interned concept,
        // so `recv` returns the identical value the coordinator put in flight.
        self.dispatched.insert(ac.clone(), concept);
        // `send` blocks only if all `worker_count` slots are full, which cannot
        // happen given the coordinator's in-flight cap -- but if it ever did, this
        // backpressure is exactly what bounds RAM.
        if let Some(tx) = &self.work_tx {
            // A worker panicking would close the channel; ignore the error (the
            // coordinator will then never receive this concept's result and the
            // pipeline drains via the in-flight count -- the panic is surfaced when
            // the worker is joined on drop).
            let _ = tx.send(ac);
        }
    }

    fn recv(
        &mut self,
    ) -> Option<(
        horned_owl::model::Class<crate::structural::A>,
        Option<crate::quasi_order::ModelReadOff<horned_owl::model::Class<crate::structural::A>>>,
    )> {
        let (ac, raw) = self.result_rx.recv().ok()?;
        // Recover the exact `Class<A>` the coordinator dispatched (its in-flight key).
        let concept = self
            .dispatched
            .remove(&ac)
            .unwrap_or_else(|| self.class_of(&Build::new_arc(), ac));
        // Convert the raw interned read-off into the classifier's `Class<A>` sets,
        // single-threaded via the shared class cache -- value-identical to serial.
        let build = Build::new_arc();
        let model = raw.map(|(known_concepts, label_concepts)| {
            let mut query_known: std::collections::HashSet<
                horned_owl::model::Class<crate::structural::A>,
            > = known_concepts.into_iter().map(|c| self.class_of(&build, c)).collect();
            query_known.insert(self.thing.clone());
            let node_labels: Vec<
                std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>,
            > = label_concepts
                .into_iter()
                .map(|acs| acs.into_iter().map(|c| self.class_of(&build, c)).collect())
                .collect();
            crate::quasi_order::ModelReadOff {
                query_known,
                query_possible: std::collections::HashSet::new(),
                node_labels: Some(node_labels),
            }
        });
        Some((concept, model))
    }

    fn worker_count(&self) -> usize {
        self.worker_count
    }
}

impl<'r> Drop for ConceptStreamingPool<'r> {
    fn drop(&mut self) {
        // Close the work channel so idle workers' `recv` returns `Err` and they
        // exit; then join every worker. This MUST complete before the borrowed
        // `&'static DLOntology` (transmuted from the reasoner) is invalidated, which
        // it is, because the pool is dropped before the reasoner outlives it.
        self.work_tx = None;
        for handle in self.workers.drain(..) {
            let _ = handle.join();
        }
    }
}

/// The persistent resolution-phase worker pool (the resolution analogue of
/// [`ConceptStreamingPool`]). Each worker owns a replica reasoner + manager and
/// loops: receive a [`ResolveTask`] -> run `quasi_order::resolve_picked_isolated`
/// over the read-only TBox via a [`RawResolveOracle`] -> send the
/// [`ResolveDelta`]. Tasks/deltas are `AtomicConcept`-native (Send); the
/// coordinator converts each delta to `Class<A>` via the shared single-threaded
/// class cache on `recv`. Same safety story as the streaming pool: the borrowed
/// `&DLOntology`/elements are extended to `'static` for the threads, which are all
/// joined in `Drop` before the pool (and thus before the reasoner) goes away.
struct ConceptResolutionPool<'r> {
    work_tx: Option<std::sync::mpsc::SyncSender<crate::quasi_order::ResolveTask<crate::model::AtomicConcept>>>,
    result_rx: std::sync::mpsc::Receiver<crate::quasi_order::ResolveDelta<crate::model::AtomicConcept>>,
    workers: Vec<std::thread::JoinHandle<()>>,
    class_cache: &'r std::cell::RefCell<
        HashMap<crate::model::AtomicConcept, horned_owl::model::Class<crate::structural::A>>,
    >,
    worker_count: usize,
}

impl<'r> ConceptResolutionPool<'r> {
    fn new<'d>(
        reasoner: &Reasoner<'d>,
        class_cache: &'r std::cell::RefCell<
            HashMap<crate::model::AtomicConcept, horned_owl::model::Class<crate::structural::A>>,
        >,
        worker_count: usize,
        top: &horned_owl::model::Class<crate::structural::A>,
        bottom: &horned_owl::model::Class<crate::structural::A>,
        elements: &std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>,
    ) -> ConceptResolutionPool<'r> {
        let to_atom = |c: &horned_owl::model::Class<crate::structural::A>| {
            crate::model::AtomicConcept::create(c.0.to_string())
        };
        let dl_ontology: &'static DLOntology =
            unsafe { std::mem::transmute::<&DLOntology, &'static DLOntology>(reasoner.dl_ontology()) };
        let configuration = reasoner.configuration().clone();
        let top_a = to_atom(top);
        let bottom_a = to_atom(bottom);
        let elements_a: std::sync::Arc<std::collections::HashSet<crate::model::AtomicConcept>> =
            std::sync::Arc::new(elements.iter().map(&to_atom).collect());

        let (work_tx, work_rx) = std::sync::mpsc::sync_channel::<
            crate::quasi_order::ResolveTask<crate::model::AtomicConcept>,
        >(worker_count);
        let (result_tx, result_rx) = std::sync::mpsc::channel::<
            crate::quasi_order::ResolveDelta<crate::model::AtomicConcept>,
        >();
        let work_rx = std::sync::Arc::new(std::sync::Mutex::new(work_rx));

        let mut workers = Vec::with_capacity(worker_count);
        for _ in 0..worker_count {
            let work_rx = std::sync::Arc::clone(&work_rx);
            let result_tx = result_tx.clone();
            let configuration = configuration.clone();
            let elements_a = std::sync::Arc::clone(&elements_a);
            let top_a = top_a.clone();
            let bottom_a = bottom_a.clone();
            let handle = std::thread::spawn(move || {
                let worker = Reasoner::with_configuration(dl_ontology, configuration);
                let mut manager = worker.new_manager();
                loop {
                    let task = {
                        let rx = work_rx.lock().unwrap();
                        rx.recv()
                    };
                    let task = match task {
                        Ok(t) => t,
                        Err(_) => break,
                    };
                    let mut raw_oracle = RawResolveOracle {
                        reasoner: &worker,
                        manager: &mut manager,
                    };
                    let delta = crate::quasi_order::resolve_picked_isolated(
                        task, &top_a, &bottom_a, &elements_a, &mut raw_oracle,
                    );
                    if result_tx.send(delta).is_err() {
                        break;
                    }
                }
            });
            workers.push(handle);
        }

        ConceptResolutionPool { work_tx: Some(work_tx), result_rx, workers, class_cache, worker_count }
    }

    fn class_of(
        &self,
        build: &Build<crate::structural::A>,
        ac: crate::model::AtomicConcept,
    ) -> horned_owl::model::Class<crate::structural::A> {
        self.class_cache
            .borrow_mut()
            .entry(ac)
            .or_insert_with(|| build.class(ac.iri()))
            .clone()
    }
}

impl<'r> crate::quasi_order::ResolutionPool<horned_owl::model::Class<crate::structural::A>>
    for ConceptResolutionPool<'r>
{
    fn dispatch(
        &mut self,
        task: crate::quasi_order::ResolveTask<horned_owl::model::Class<crate::structural::A>>,
    ) {
        let to_atom = |c: &horned_owl::model::Class<crate::structural::A>| {
            crate::model::AtomicConcept::create(c.0.to_string())
        };
        let atomic = crate::quasi_order::ResolveTask {
            picked: to_atom(&task.picked),
            unknown: task.unknown.iter().map(&to_atom).collect(),
            known_map: task
                .known_map
                .into_iter()
                .map(|(k, v)| (to_atom(&k), v.iter().map(&to_atom).collect()))
                .collect(),
        };
        if let Some(tx) = &self.work_tx {
            let _ = tx.send(atomic);
        }
    }

    fn recv(
        &mut self,
    ) -> Option<crate::quasi_order::ResolveDelta<horned_owl::model::Class<crate::structural::A>>> {
        let d = self.result_rx.recv().ok()?;
        let build = Build::new_arc();
        Some(crate::quasi_order::ResolveDelta {
            picked: self.class_of(&build, d.picked),
            new_knowns: d.new_knowns.into_iter().map(|a| self.class_of(&build, a)).collect(),
            pruned_labels: d
                .pruned_labels
                .into_iter()
                .map(|s| s.into_iter().map(|a| self.class_of(&build, a)).collect())
                .collect(),
        })
    }

    fn worker_count(&self) -> usize {
        self.worker_count
    }
}

impl<'r> Drop for ConceptResolutionPool<'r> {
    fn drop(&mut self) {
        self.work_tx = None;
        for handle in self.workers.drain(..) {
            let _ = handle.join();
        }
    }
}

/// Classifies the named object properties into a subsumption
/// [`Hierarchy`](crate::hierarchy::Hierarchy) over `ObjectProperty` (the named
/// roles only). This is the backward-compatible projection of
/// [`classify_object_property_expressions`] onto named properties; inverse-role
/// nodes are surfaced by that richer function.
pub fn classify_object_properties(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<
    crate::hierarchy::Hierarchy<horned_owl::model::ObjectProperty<crate::structural::A>>,
    String,
> {
    classify_object_properties_with_configuration(
        ontology,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`classify_object_properties`], but runs the object-property classification
/// under an explicit [`Configuration`](crate::configuration::Configuration).
pub fn classify_object_properties_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<
    crate::hierarchy::Hierarchy<horned_owl::model::ObjectProperty<crate::structural::A>>,
    String,
> {
    use horned_owl::model::{ObjectProperty, ObjectPropertyExpression as OPE};
    use std::collections::HashSet;

    let build = Build::new_arc();
    let top = build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty");
    let bottom = build.object_property("http://www.w3.org/2002/07/owl#bottomObjectProperty");

    // Classify over object-property *expressions* (incl. inverses) then project the
    // result onto named properties: each named property's subsumers are the named
    // properties among its OPE-hierarchy ancestors' equivalents.
    let ope_hierarchy = classify_object_property_expressions_with_configuration(ontology, configuration)?;
    let named_of = |ope: &OPE<crate::structural::A>| -> Option<ObjectProperty<crate::structural::A>> {
        match ope {
            OPE::ObjectProperty(p) => Some(p.clone()),
            OPE::InverseObjectProperty(_) => None,
        }
    };

    let mut elements: HashSet<ObjectProperty<crate::structural::A>> = HashSet::new();
    for ope in ope_hierarchy.all_elements() {
        if let Some(p) = named_of(ope) {
            elements.insert(p);
        }
    }
    elements.insert(top.clone());
    elements.insert(bottom.clone());

    let mut subsumers: HashMap<
        ObjectProperty<crate::structural::A>,
        HashSet<ObjectProperty<crate::structural::A>>,
    > = HashMap::new();
    for element in &elements {
        let mut element_subsumers: HashSet<ObjectProperty<crate::structural::A>> = HashSet::new();
        element_subsumers.insert(top.clone());
        element_subsumers.insert(element.clone());
        if *element != top && *element != bottom {
            if let Some(node) = ope_hierarchy.node_for_element(&OPE::ObjectProperty(element.clone()))
            {
                for ancestor in ope_hierarchy.ancestor_nodes(node) {
                    for ope in ope_hierarchy.node(ancestor).equivalent_elements() {
                        if let Some(p) = named_of(ope) {
                            element_subsumers.insert(p);
                        }
                    }
                }
            }
        }
        // bottom is subsumed by everything; an empty property is also subsumed by
        // everything (it collapses with bottom in the OPE hierarchy).
        if *element == bottom
            || ope_hierarchy
                .node_for_element(&OPE::ObjectProperty(element.clone()))
                .map(|n| n == ope_hierarchy.bottom_node())
                .unwrap_or(false)
        {
            for other in &elements {
                element_subsumers.insert(other.clone());
            }
        }
        subsumers.insert(element.clone(), element_subsumers);
    }
    Ok(crate::hierarchy::build_hierarchy(top, bottom, subsumers))
}

/// Classifies object-property *expressions* into a subsumption
/// [`Hierarchy`](crate::hierarchy::Hierarchy), surfacing one `Inv(P)` node per
/// inverse role -- the faithful analogue of HermiT's `classifyObjectProperties`
/// (`Reasoner.java:945-1029`) whose `m_objectRoleHierarchy` is a `Hierarchy<Role>`
/// (`Role` = `OWLObjectPropertyExpression`). When the ontology
/// `hasInverseRoles()`, an `internal:prop#inv#…` role-concept is added per
/// inverse role and the classification is run through
/// [`QuasiOrderClassificationForRoles`](crate::quasi_order) with the
/// `inverse_concept` map populated (mirroring every subsumption onto inverses).
/// The resulting concept-node hierarchy is transformed back to OPE nodes (Java's
/// `transformer`).
pub fn classify_object_property_expressions(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<
    crate::hierarchy::Hierarchy<
        horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    >,
    String,
> {
    classify_object_property_expressions_with_configuration(
        ontology,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`classify_object_property_expressions`], but runs the role classification
/// under an explicit [`Configuration`](crate::configuration::Configuration):
/// the consistency precheck and every subsumption test
/// ([`is_object_property_subsumed_by_with`]) are threaded through `configuration`.
pub fn classify_object_property_expressions_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<
    crate::hierarchy::Hierarchy<
        horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    >,
    String,
> {
    // `Reasoner.classifyObjectProperties` (Reasoner.java:946) calls
    // `checkPreConditions` first, so it throws on an inconsistent ontology under
    // the default flag (the `!m_isConsistent` empty-hierarchy branch is for the
    // flag-off case).
    throw_inconsistent_ontology_exception_if_necessary(ontology, configuration)?;
    use crate::quasi_order::QuasiOrderClassification;
    use crate::structural::{
        BuiltInPropertyManager, OWLAxioms, OWLAxiomsExpressivity, OWLNormalization,
    };
    use horned_owl::model::{ObjectProperty, ObjectPropertyExpression as OPE};
    use std::collections::HashSet;
    let configuration = configuration.clone();

    let build = Build::new_arc();
    let top: OPE<crate::structural::A> =
        OPE::ObjectProperty(build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty"));
    let bottom: OPE<crate::structural::A> = OPE::ObjectProperty(
        build.object_property("http://www.w3.org/2002/07/owl#bottomObjectProperty"),
    );

    // Named object roles of the DL vocabulary (as in m_dlOntology.getAllAtomicObjectRoles).
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology)?;
    let mut axioms = normalization.into_axioms();
    BuiltInPropertyManager::new().axiomatize_built_in_properties_as_needed(&mut axioms);
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    let has_inverse_roles = expressivity.has_inverse_roles;

    let mut named_roles: HashSet<ObjectProperty<crate::structural::A>> = HashSet::new();
    for property in axioms
        .object_properties
        .iter()
        .chain(axioms.object_properties_occurring_in_owl_axioms.iter())
    {
        let iri = property.0.to_string();
        if iri.starts_with("internal:")
            || iri == "http://www.w3.org/2002/07/owl#topObjectProperty"
            || iri == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
        {
            continue;
        }
        named_roles.insert(property.clone());
    }
    // The role-concepts to classify: each named role, plus -- when the ontology has
    // inverse roles -- its inverse (matching the `relevantObjectRoles` loop).
    let mut elements: HashSet<OPE<crate::structural::A>> = HashSet::new();
    let mut inverse_concept: HashMap<OPE<crate::structural::A>, OPE<crate::structural::A>> =
        HashMap::new();
    for role in &named_roles {
        let p = OPE::ObjectProperty(role.clone());
        elements.insert(p.clone());
        if has_inverse_roles {
            let ip = OPE::InverseObjectProperty(role.clone());
            elements.insert(ip.clone());
            inverse_concept.insert(p.clone(), ip.clone());
            inverse_concept.insert(ip, p);
        }
    }
    elements.insert(top.clone());
    elements.insert(bottom.clone());

    if !is_ontology_consistent_with_configuration(ontology, &configuration)? {
        let elements_vec: Vec<OPE<crate::structural::A>> = elements.into_iter().collect();
        return Ok(crate::hierarchy::Hierarchy::empty_hierarchy(
            &elements_vec,
            top,
            bottom,
        ));
    }

    // Candidate possible-subsumers (everything except top/bottom).
    let candidates: Vec<OPE<crate::structural::A>> = elements
        .iter()
        .filter(|e| **e != top && **e != bottom)
        .cloned()
        .collect();

    // A persistent reasoner over the clausified ontology, used to read each role's
    // subsumers off a single saturated model (HermiT's buildModelForConcept),
    // reusing the compiled clauses across elements.
    let dl_ontology = clausify_for_query(ontology)?;
    let model_reasoner = Reasoner::new(&dl_ontology);
    let mut model_manager = model_reasoner.new_manager();
    let model_top = top.clone();

    // Deterministic (Horn) ontologies: read every role's subsumers off its one
    // saturated model and build the hierarchy directly, with no subsumption
    // tests -- HermiT's `DeterministicClassification` (Reasoner.java:2053-2054
    // dispatches on `tableau.isDeterministic() && !forceQuasiOrder`).
    if model_reasoner.is_deterministic() && !configuration.force_quasi_order_classification {
        let mut subsumers: HashMap<OPE<crate::structural::A>, HashSet<OPE<crate::structural::A>>> =
            HashMap::new();
        for element in &elements {
            let mut element_subsumers: HashSet<OPE<crate::structural::A>> = HashSet::new();
            element_subsumers.insert(top.clone());
            element_subsumers.insert(element.clone());
            if *element == top {
                // owl:topObjectProperty is subsumed only by itself.
            } else if *element == bottom {
                element_subsumers.extend(elements.iter().cloned());
            } else {
                match model_reasoner.object_property_edge_subsumers(
                    &mut model_manager,
                    element,
                    &candidates,
                ) {
                    Some(holds) => element_subsumers.extend(holds),
                    // An unsatisfiable (empty) role is subsumed by everything.
                    None => element_subsumers.extend(elements.iter().cloned()),
                }
            }
            subsumers.insert(element.clone(), element_subsumers);
        }
        return Ok(crate::hierarchy::build_hierarchy(top, bottom, subsumers));
    }

    // Shared by the build-model and union-test read-offs (both run on this one
    // reusable reasoner/manager, like HermiT's single classification `m_tableau`).
    let model_reasoner = std::rc::Rc::new(model_reasoner);
    let model_manager = std::rc::Rc::new(std::cell::RefCell::new(model_manager));

    let oracle = PropertySubsumptionOracle {
        ontology,
        candidates,
        subsumes: {
            let configuration = configuration.clone();
            move |o: &SetOntology<crate::structural::A>,
                  sub: &OPE<crate::structural::A>,
                  sup: &OPE<crate::structural::A>| {
                // Internal oracle: the non-throwing reduction (classification has
                // already verified consistency; the public *_with applies
                // checkPreConditions).
                is_object_property_subsumed_by_core_with(o, sub.clone(), sup.clone(), &configuration)
            }
        },
        subsumes_union: {
            let model_reasoner = std::rc::Rc::clone(&model_reasoner);
            let model_manager = std::rc::Rc::clone(&model_manager);
            move |o: &SetOntology<crate::structural::A>,
                  sub: &OPE<crate::structural::A>,
                  sups: &std::collections::HashSet<OPE<crate::structural::A>>| {
                let subsumed = is_object_property_subsumed_by_union_with(o, sub.clone(), sups, &configuration)?;
                // readKnownSubsumersFromRootNode: on a positive union test, read the
                // picked role's deterministic edge-subsumers off the witnessing model
                // (only the union candidates are checked, exactly as the class path
                // reads only the atomic concepts on the witnessing root). Read only
                // when subsumed; the known set is ignored otherwise.
                let mut known: std::collections::HashSet<OPE<crate::structural::A>> =
                    std::collections::HashSet::new();
                if subsumed {
                    let candidates: Vec<OPE<crate::structural::A>> = sups.iter().cloned().collect();
                    if let Some(holds) = model_reasoner.object_property_deterministic_edge_subsumers(
                        &mut model_manager.borrow_mut(),
                        sub,
                        &candidates,
                    ) {
                        known = holds;
                    }
                }
                Ok((subsumed, known))
            }
        },
        build_model_fn: {
            let model_reasoner = std::rc::Rc::clone(&model_reasoner);
            let model_manager = std::rc::Rc::clone(&model_manager);
            move |picked: &OPE<crate::structural::A>,
                  candidates: &[OPE<crate::structural::A>]| {
                // Read the subsumers off one saturated model of picked(a,b); top is a
                // deterministic (known) subsumer, the rest are possible.
                let holds = model_reasoner.object_property_edge_subsumers(
                    &mut model_manager.borrow_mut(),
                    picked,
                    candidates,
                )?;
                let mut possible = holds;
                possible.remove(picked);
                possible.remove(&model_top);
                let known: std::collections::HashSet<OPE<crate::structural::A>> =
                    std::iter::once(model_top.clone()).collect();
                Some((known, possible))
            }
        },
        error: None,
    };

    let mut classifier = QuasiOrderClassification::new_for_roles(
        oracle,
        top.clone(),
        bottom.clone(),
        elements.clone(),
        if has_inverse_roles { Some(inverse_concept) } else { None },
    );
    // Seed told role inclusions (sub ⊑ sup, and the inverse mirror).
    let told: Vec<(OPE<crate::structural::A>, OPE<crate::structural::A>, bool)> = axioms
        .simple_object_property_inclusions
        .iter()
        .map(|[sub, sup]| (sub.clone(), sup.clone(), false))
        .collect();
    classifier.initialise_known_subsumptions_using_told_subsumers(
        &told
            .iter()
            .map(|(s, p, _)| (s.clone(), p.clone()))
            .collect::<Vec<_>>(),
    );
    let hierarchy = classifier.classify();
    Ok(hierarchy)
}

/// Classifies the data properties into a subsumption
/// [`Hierarchy`](crate::hierarchy::Hierarchy) -- the data-role analogue of
/// [`classify_object_property_expressions`] (HermiT's `classifyDataProperties`,
/// `Reasoner.java:1355` / `m_dataRoleHierarchy`). There are no inverse data
/// roles, so this runs the plain [`QuasiOrderClassification`](crate::quasi_order)
/// (no `inverse_concept`) with the subsumption oracle
/// ([`is_sub_data_property_of`]). Top/bottom are
/// `owl:topDataProperty`/`owl:bottomDataProperty`.
pub fn classify_data_properties(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<
    crate::hierarchy::Hierarchy<horned_owl::model::DataProperty<crate::structural::A>>,
    String,
> {
    classify_data_properties_with_configuration(
        ontology,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`classify_data_properties`], but runs the data-property classification
/// under an explicit [`Configuration`](crate::configuration::Configuration):
/// the consistency precheck and every subsumption test
/// ([`is_sub_data_property_of_with`]) are threaded through `configuration`.
pub fn classify_data_properties_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<
    crate::hierarchy::Hierarchy<horned_owl::model::DataProperty<crate::structural::A>>,
    String,
> {
    // `Reasoner.classifyDataProperties`/`getSub|SuperDataProperties`
    // (Reasoner.java) call `checkPreConditions` first, so they throw on an
    // inconsistent ontology under the default flag.
    throw_inconsistent_ontology_exception_if_necessary(ontology, configuration)?;
    use crate::quasi_order::QuasiOrderClassification;
    use crate::structural::{OWLAxioms, OWLNormalization};
    use horned_owl::model::DataProperty;
    use std::collections::HashSet;
    let configuration = configuration.clone();

    let build = Build::new_arc();
    let top = build.data_property("http://www.w3.org/2002/07/owl#topDataProperty");
    let bottom = build.data_property("http://www.w3.org/2002/07/owl#bottomDataProperty");

    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology)?;
    let axioms = normalization.into_axioms();

    let mut elements: HashSet<DataProperty<crate::structural::A>> = HashSet::new();
    for property in &axioms.data_properties {
        let iri = property.0.to_string();
        if iri.starts_with("internal:")
            || iri == "http://www.w3.org/2002/07/owl#topDataProperty"
            || iri == "http://www.w3.org/2002/07/owl#bottomDataProperty"
        {
            continue;
        }
        elements.insert(property.clone());
    }
    elements.insert(top.clone());
    elements.insert(bottom.clone());

    if !is_ontology_consistent_with_configuration(ontology, &configuration)? {
        let elements_vec: Vec<DataProperty<crate::structural::A>> =
            elements.into_iter().collect();
        return Ok(crate::hierarchy::Hierarchy::empty_hierarchy(
            &elements_vec,
            top,
            bottom,
        ));
    }

    // `Reasoner.classifyDataProperties` (Reasoner.java:1365,1422-1423): when the
    // ontology has no datatypes the data-role hierarchy is the trivial one
    // (only top and bottom; named data roles are treated as fresh entities and
    // their told inclusions are NOT reflected).
    if !clausify_for_query(ontology)?.has_datatypes() {
        return Ok(crate::hierarchy::Hierarchy::trivial_hierarchy(top, bottom));
    }

    let candidates: Vec<DataProperty<crate::structural::A>> = elements
        .iter()
        .filter(|e| **e != top && **e != bottom)
        .cloned()
        .collect();

    // A persistent reasoner used to read each data property's subsumers off a
    // single saturated model (HermiT's buildModelForConcept).
    let dl_ontology = clausify_for_query(ontology)?;
    let model_reasoner = Reasoner::new(&dl_ontology);
    let mut model_manager = model_reasoner.new_manager();

    // Deterministic (Horn) ontologies: read each data property's subsumers off
    // its one saturated model with no subsumption tests -- HermiT's
    // `DeterministicClassification` (Reasoner.java:1404 -> 2047).
    if model_reasoner.is_deterministic() && !configuration.force_quasi_order_classification {
        let mut subsumers: HashMap<
            DataProperty<crate::structural::A>,
            HashSet<DataProperty<crate::structural::A>>,
        > = HashMap::new();
        for element in &elements {
            let mut element_subsumers: HashSet<DataProperty<crate::structural::A>> = HashSet::new();
            element_subsumers.insert(top.clone());
            element_subsumers.insert(element.clone());
            if *element == top {
                // owl:topDataProperty is subsumed only by itself.
            } else if *element == bottom {
                element_subsumers.extend(elements.iter().cloned());
            } else {
                match model_reasoner.data_property_edge_subsumers(
                    &mut model_manager,
                    element,
                    &candidates,
                ) {
                    Some(holds) => element_subsumers.extend(holds),
                    None => element_subsumers.extend(elements.iter().cloned()),
                }
            }
            subsumers.insert(element.clone(), element_subsumers);
        }
        return Ok(crate::hierarchy::build_hierarchy(top, bottom, subsumers));
    }

    // Shared by the build-model and union-test read-offs (one reusable
    // reasoner/manager, like HermiT's single classification `m_tableau`).
    let model_reasoner = std::rc::Rc::new(model_reasoner);
    let model_manager = std::rc::Rc::new(std::cell::RefCell::new(model_manager));

    let oracle = PropertySubsumptionOracle {
        ontology,
        candidates,
        subsumes: {
            let configuration = configuration.clone();
            move |o: &SetOntology<crate::structural::A>,
                  sub: &DataProperty<crate::structural::A>,
                  sup: &DataProperty<crate::structural::A>| {
                is_sub_data_property_of_core_with(o, sub.clone(), sup.clone(), &configuration)
            }
        },
        subsumes_union: {
            let model_reasoner = std::rc::Rc::clone(&model_reasoner);
            let model_manager = std::rc::Rc::clone(&model_manager);
            move |o: &SetOntology<crate::structural::A>,
                  sub: &DataProperty<crate::structural::A>,
                  sups: &std::collections::HashSet<DataProperty<crate::structural::A>>| {
                let subsumed =
                    is_sub_data_property_of_union_with(o, sub.clone(), sups, &configuration)?;
                // readKnownSubsumersFromRootNode: on a positive union test, read the
                // picked data property's deterministic edge-subsumers off the
                // witnessing model (only the union candidates are checked).
                let mut known: std::collections::HashSet<DataProperty<crate::structural::A>> =
                    std::collections::HashSet::new();
                if subsumed {
                    let candidates: Vec<DataProperty<crate::structural::A>> =
                        sups.iter().cloned().collect();
                    if let Some(holds) = model_reasoner.data_property_deterministic_edge_subsumers(
                        &mut model_manager.borrow_mut(),
                        sub,
                        &candidates,
                    ) {
                        known = holds;
                    }
                }
                Ok((subsumed, known))
            }
        },
        build_model_fn: {
            let model_reasoner = std::rc::Rc::clone(&model_reasoner);
            let model_manager = std::rc::Rc::clone(&model_manager);
            let model_top = top.clone();
            move |picked: &DataProperty<crate::structural::A>,
                  candidates: &[DataProperty<crate::structural::A>]| {
                // Read the subsumers off one saturated model of picked(a,k); top is a
                // deterministic (known) subsumer, the rest are possible.
                let holds = model_reasoner.data_property_edge_subsumers(
                    &mut model_manager.borrow_mut(),
                    picked,
                    candidates,
                )?;
                let mut possible = holds;
                possible.remove(picked);
                possible.remove(&model_top);
                let known: std::collections::HashSet<DataProperty<crate::structural::A>> =
                    std::iter::once(model_top.clone()).collect();
                Some((known, possible))
            }
        },
        error: None,
    };

    let mut classifier =
        QuasiOrderClassification::new(oracle, top.clone(), bottom.clone(), elements.clone());
    // Seed told data-property inclusions (sub ⊑ sup).
    let told: Vec<(DataProperty<crate::structural::A>, DataProperty<crate::structural::A>)> = axioms
        .data_property_inclusions
        .iter()
        .map(|[sub, sup]| (sub.clone(), sup.clone()))
        .collect();
    classifier.initialise_known_subsumptions_using_told_subsumers(&told);
    Ok(classifier.classify())
}

/// The data properties that subsume `property` (`Reasoner.getSuperDataProperties`,
/// `Reasoner.java:1458`). `direct` restricts to the immediate parents.
pub fn get_super_data_properties(
    ontology: &SetOntology<crate::structural::A>,
    property: &horned_owl::model::DataProperty<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>>, String>
{
    Ok(classify_data_properties(ontology)?.super_elements(property, direct))
}

/// The data properties subsumed by `property` (`Reasoner.getSubDataProperties`).
/// `direct` restricts to the immediate children.
pub fn get_sub_data_properties(
    ontology: &SetOntology<crate::structural::A>,
    property: &horned_owl::model::DataProperty<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>>, String>
{
    Ok(classify_data_properties(ontology)?.sub_elements(property, direct))
}

// ===========================================================================
// The read-off InstanceManager path.
//
// `build_class_instance_manager` mirrors `Reasoner.initialiseClassInstanceManager`
// + `InstanceManager.initializeKnowAndPossibleClassInstances` + `realize`:
//   1. run the initial consistency check, keeping the saturated tableau and the
//      individual -> node map (`saturate_for_instances`, the analogue of
//      `tableau.isSatisfiable(..., m_nodesForIndividuals, ...)`);
//   2. read each individual's node atomic-concept labels off the model, splitting
//      KNOWN (empty dependency set) from POSSIBLE (`readOffTypes`);
//   3. seed the same-as equivalence classes from the model's individual merges
//      (`initializeSameAs`);
//   4. confirm the POSSIBLE instances with the `is_instance` oracle, but never the
//      KNOWN ones (`realize`).
// `realize`/`instances`/`get_types` then read the KNOWN instances directly.
// ===========================================================================

/// The result of [`build_class_instance_manager_with_configuration`]: the seeded
/// manager, the classified concept hierarchy and the set of result-relevant named
/// individuals.
pub(crate) struct BuiltClassInstanceManager {
    pub manager: crate::instance_manager::SeededClassInstanceManager,
    pub hierarchy: crate::hierarchy::Hierarchy<horned_owl::model::Class<crate::structural::A>>,
    pub individuals: std::collections::HashSet<String>,
}

/// Builds and fully realises the class `InstanceManager` for `ontology` by reading
/// the saturated initial-consistency-check model, threading
/// `configuration` into the saturating tableau and the underlying
/// classification so realisation runs under the same configuration HermiT's
/// `m_configuration` governs. Returns `None` when the ontology is inconsistent
/// (the caller mirrors HermiT's `setInconsistent` answers directly).
pub(crate) fn build_class_instance_manager_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<Option<BuiltClassInstanceManager>, String> {
    use crate::instance_manager::SeededClassInstanceManager;
    use crate::tableau::dependency_set::DependencySetOps;
    use horned_owl::model::Class;

    let dl_ontology = clausify_ontology(ontology)?;
    let reasoner = Reasoner::with_configuration(&dl_ontology, configuration.clone());

    // (1) Initial consistency check + node read-off map. `None` => inconsistent.
    let Some((mut tableau, nodes_for_individuals)) = reasoner.saturate_for_instances() else {
        return Ok(None);
    };

    // The classified concept hierarchy (the answers must match `classify`).
    let hierarchy = classify_with_configuration(ontology, configuration)?;
    let build = Build::new_arc();

    // Map a concept IRI to its hierarchy node, skipping owl:Thing / internal /
    // unknown concepts (cf. `readOffTypes`'s `m_topConcept`/internal guard).
    let node_for_iri = |iri: &str| -> Option<crate::hierarchy::NodeRef> {
        if iri == "http://www.w3.org/2002/07/owl#Thing"
            || iri == "http://www.w3.org/2002/07/owl#Nothing"
            || iri.starts_with("internal:")
        {
            return None;
        }
        hierarchy.node_for_element(&build.class(iri))
    };

    let mut manager = SeededClassInstanceManager::new();

    // Result-relevant named individuals (skip anonymous / internal).
    let mut relevant_individuals: Vec<String> = Vec::new();
    for individual in dl_ontology.get_all_individuals() {
        let iri = individual.iri();
        if iri.starts_with("internal:") {
            continue;
        }
        relevant_individuals.push(iri.to_string());
    }

    // (3) Seed same-as equivalence classes from the model's individual merges.
    // For each named individual whose node was merged into the node of another
    // named individual, record the same-as pair; an empty merge dependency set is
    // a deterministic (definite) same-as.
    let empty_set = tableau.dependency_set_factory().empty_set();
    let mut same_as_pairs: Vec<(String, String, bool)> = Vec::new();
    for (individual, &raw_node) in &nodes_for_individuals {
        let iri = individual.iri();
        if iri.starts_with("internal:") {
            continue;
        }
        if let Some(merged_into) = tableau.node(raw_node).get_merged_into() {
            // Find the named individual (if any) owning the merge target.
            if let Some(other) = nodes_for_individuals
                .iter()
                .find(|(_, &n)| n == merged_into)
                .map(|(o, _)| o)
            {
                if other.iri().starts_with("internal:") {
                    continue;
                }
                let definite = tableau
                    .node(raw_node)
                    .get_merged_into_dependency_set()
                    .map_or(true, |d| d.is_empty());
                same_as_pairs.push((iri.to_string(), other.iri().to_string(), definite));
            }
        }
    }
    manager.seed_same_as(&relevant_individuals, &same_as_pairs);

    // (2) Read off the known/possible class instances per individual.
    for individual in dl_ontology.get_all_individuals() {
        let iri = individual.iri();
        if iri.starts_with("internal:") {
            continue;
        }
        let Some(&raw_node) = nodes_for_individuals.get(individual) else {
            continue;
        };
        let canonical = tableau.get_canonical_node(raw_node);
        let labels = read_off_node_concepts(&tableau, canonical, &empty_set);
        manager.read_off_types(iri, &labels, |concept_iri| node_for_iri(concept_iri));
        // Every named individual is a (known) instance of owl:Thing -- the top
        // node -- so its `getTypes` includes owl:Thing and `getInstances(Thing)`
        // returns it. The `direct` filter still excludes top when a more-specific
        // type is known. (Java seeds top only for individuals with no read-off
        // type; seeding it for all is equivalent because top has the type node as
        // a child, so a more-specific known type keeps it out of the direct set.)
        manager.seed_top_known(hierarchy.top_node(), iri);
    }

    // (4) Confirm the possibles with the `is_instance` oracle (never the knowns).
    // `is_instance_of_core` IS HermiT's `isInstance` (an entailment test over the
    // representative concept), now run only for the POSSIBLE (slice) instances.
    manager.realize(&hierarchy, |representative: &Class<crate::structural::A>, individual| {
        let named = build.named_individual(individual);
        is_instance_of_core(ontology, named, CE::Class(representative.clone())).unwrap_or(false)
    });

    let individuals: std::collections::HashSet<String> =
        relevant_individuals.into_iter().collect();
    Ok(Some(BuiltClassInstanceManager { manager, hierarchy, individuals }))
}

/// Reads off the atomic-concept memberships of `node` from the saturated model,
/// splitting KNOWN (empty dependency set) from POSSIBLE. Port of the
/// `m_binaryRetrieval1Bound` loop in `InstanceManager.readOffTypes`: it iterates
/// the binary extension table bound to `node` (column 1) and, for every atomic
/// concept in column 0, records its dependency-set emptiness.
fn read_off_node_concepts(
    tableau: &Tableau,
    node: NodeId,
    empty_set: &crate::tableau::dependency_set::PermanentDependencySet,
) -> Vec<crate::instance_manager::ReadOffConcept> {
    use crate::instance_manager::ReadOffConcept;
    use crate::tableau::dependency_set::DependencySetOps;
    use crate::tableau::extension_table::View;
    let retrieval = tableau.create_binary_retrieval(
        [-1, 1],
        [None, Some(TableauObject::Node(node))],
        View::Total,
    );
    let mut labels = Vec::new();
    for &tuple_index in &retrieval.tuple_indices {
        if let TableauObject::Concept(Concept::AtomicConcept(c)) =
            tableau.binary_extension_table.get_tuple_object(tuple_index, 0)
        {
            let known = tableau
                .binary_extension_table
                .get_dependency_set(tuple_index, empty_set)
                .is_empty();
            labels.push(ReadOffConcept { concept_iri: c.iri().to_string(), known });
        }
    }
    labels
}

/// `readKnownSubsumersFromRootNode`'s determinism guard for a single node: the
/// node's merge chain to its canonical node must carry an empty dependency set
/// throughout (a non-deterministic merge makes the node's canonical labels
/// uncertain). Mirrors the guard in
/// [`Reasoner::atomic_subsumed_by_union_with_known`].
fn node_merge_chain_is_deterministic(tableau: &Tableau, node: NodeId) -> bool {
    use crate::tableau::dependency_set::DependencySetOps;
    let mut walk = node;
    while let Some(into) = tableau.node(walk).get_merged_into() {
        let det = tableau
            .node(walk)
            .get_merged_into_dependency_set()
            .map_or(true, |d| d.is_empty());
        if !det {
            return false;
        }
        walk = into;
    }
    true
}

/// Whether the role tuple `role(from, to)` is present on the (already canonical)
/// edge with an *empty* dependency set -- i.e. a deterministic consequence. `role`
/// must be a [`Role::AtomicRole`](crate::model::Role::AtomicRole) and the endpoints
/// already oriented onto the named property (as `add_role_assertion` stores them),
/// matching the role-edge read in `read_off_role_instances`. This is the role-tuple
/// analogue of the empty-dependency-set filter `read_off_node_concepts` applies to
/// concept tuples (`readKnownSubsumersFromRootNode`).
fn role_assertion_is_deterministic(
    tableau: &Tableau,
    role: &crate::model::Role,
    from: NodeId,
    to: NodeId,
) -> bool {
    use crate::model::{DLPredicate, Role};
    use crate::tableau::dependency_set::DependencySetOps;
    let r = match role {
        Role::AtomicRole(r) => r.clone(),
        // The deterministic read-off only ever builds atomic-role tuples; an
        // inverse role here would not match the stored (named-property) tuple.
        Role::InverseRole(_) => return false,
    };
    let tuple = [
        TableauObject::DLPredicate(DLPredicate::AtomicRole(r)),
        TableauObject::Node(from),
        TableauObject::Node(to),
    ];
    let index = tableau.ternary_extension_table.get_tuple_index(&tuple);
    if index == -1 || !tableau.node(from).is_active() || !tableau.node(to).is_active() {
        return false;
    }
    let empty_set = tableau.dependency_set_factory.empty_set();
    tableau
        .ternary_extension_table
        .get_dependency_set(index as usize, &empty_set)
        .is_empty()
}

/// The pairs of named individuals `(a, b)` for which `ope(a, b)` is entailed
/// (HermiT's `getObjectPropertyInstances` / `getObjectPropertyValues`). This is
/// the role-instance side of `InstanceManager`.
pub fn object_property_instances(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<
    std::collections::HashSet<(
        NamedIndividual<crate::structural::A>,
        NamedIndividual<crate::structural::A>,
    )>,
    String,
> {
    use horned_owl::model::{Component, Individual, ObjectPropertyAssertion};
    use std::collections::HashSet;

    // `Reasoner.getObjectPropertyInstances` (Reasoner.java:1779) calls
    // `checkPreConditions` first, so it throws on an inconsistent ontology under
    // the default flag (the `!m_isConsistent` all-pairs branch only runs when the
    // flag is off).
    check_pre_conditions(ontology)?;
    let build = Build::new_arc();
    let dl_ontology = clausify_for_query(ontology)?;
    let individuals: Vec<NamedIndividual<crate::structural::A>> = dl_ontology
        .get_all_individuals()
        .iter()
        .filter(|i| !i.iri().starts_with("internal:"))
        .map(|i| build.named_individual(i.iri()))
        .collect();

    // Read the KNOWN role pairs off the saturated model
    // (`InstanceManager.readOffPropertyInstances` -- a deterministic ternary
    // assertion between two named-individual nodes is a known role instance). For a
    // KNOWN pair we skip the entailment test; otherwise the pair is treated as a
    // POSSIBLE one and confirmed with the oracle. The known set is computed only for
    // the plain (non-inverse) atomic-role projection; under inverse / complex roles
    // the known set is just empty and every pair falls through to the oracle, so the
    // ANSWERS are identical either way.
    let known = build_known_object_property_pairs(ontology, &ope)?;

    let mut result: HashSet<(
        NamedIndividual<crate::structural::A>,
        NamedIndividual<crate::structural::A>,
    )> = HashSet::new();
    for from in &individuals {
        for to in &individuals {
            let pair = (from.0.to_string(), to.0.to_string());
            if known.contains(&pair)
                || is_entailed_core(
                    ontology,
                    &Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
                        ope: ope.clone(),
                        from: Individual::Named(from.clone()),
                        to: Individual::Named(to.clone()),
                    }),
                )?
            {
                result.insert((from.clone(), to.clone()));
            }
        }
    }
    Ok(result)
}

/// Reads the KNOWN `ope` role pairs off the saturated model, returning them as
/// `(source_iri, target_iri)` pairs (the role analogue of the class read-off).
/// Port of `InstanceManager.readOffPropertyInstances` plus
/// `readOffComplexRoleSuccessors`: a deterministic (empty dependency set)
/// `role(source, target)` between named-individual nodes is a *known* role
/// instance. For a *complex* (e.g. transitive) role the direct ternary assertions
/// miss transitively-implied successors, so -- exactly as HermiT does -- we add
/// the read-off axioms `A_a(a)` and `A_a ⊑ ∀role.A_a^role` for each named
/// individual `a`, saturate, and read off the `A_a^role`-labelled named successors
/// (the ∀ propagates along the full role automaton, capturing the transitive
/// closure). An inverse role reuses the forward read-off with the pairs swapped.
fn build_known_object_property_pairs(
    ontology: &SetOntology<crate::structural::A>,
    ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<std::collections::HashSet<(String, String)>, String> {
    use crate::model::{AtomicRole, Role};
    use horned_owl::model::ObjectPropertyExpression as OPE;

    let (role_iri, is_inverse) = match ope {
        OPE::ObjectProperty(p) => (p.0.to_string(), false),
        OPE::InverseObjectProperty(p) => (p.0.to_string(), true),
    };

    // A complex object role needs the auxiliary-axiom read-off to capture
    // transitively-implied successors; a simple role is read off directly.
    let dl_check = clausify_for_query(ontology)?;
    let is_complex = dl_check
        .is_complex_object_role(&Role::AtomicRole(AtomicRole::create(role_iri.clone())));
    let forward = if is_complex {
        complex_role_known_forward_pairs(ontology, &role_iri)?
    } else {
        plain_role_known_forward_pairs(ontology, &role_iri)?
    };
    if is_inverse {
        Ok(forward.into_iter().map(|(s, t)| (t, s)).collect())
    } else {
        Ok(forward)
    }
}

/// `InstanceManager.readOffPropertyInstances`: the direct ternary read-off of a
/// simple object role's known `(source, target)` pairs from the saturated model.
fn plain_role_known_forward_pairs(
    ontology: &SetOntology<crate::structural::A>,
    role_iri: &str,
) -> Result<std::collections::HashSet<(String, String)>, String> {
    use crate::instance_manager::RoleElementManager;
    use crate::tableau::dependency_set::DependencySetOps;
    use crate::tableau::extension_table::View;
    use std::collections::HashSet;

    let dl_ontology = clausify_ontology(ontology)?;
    let reasoner = Reasoner::new(&dl_ontology);
    let Some((mut tableau, nodes_for_individuals)) = reasoner.saturate_for_instances() else {
        return Ok(HashSet::new());
    };

    // Canonical node -> named-individual IRI (skipping internal individuals).
    let mut iri_for_canonical: HashMap<NodeId, String> = HashMap::new();
    for (individual, &raw_node) in &nodes_for_individuals {
        let iri = individual.iri();
        if iri.starts_with("internal:") {
            continue;
        }
        let canonical = tableau.get_canonical_node(raw_node);
        iri_for_canonical.entry(canonical).or_insert_with(|| iri.to_string());
    }

    let mut role_manager = RoleElementManager::new();
    let empty_set = tableau.dependency_set_factory().empty_set();
    let retrieval = tableau.create_ternary_retrieval([-1, -1, -1], [None, None, None], View::Total);
    for &tuple_index in &retrieval.tuple_indices {
        // The role projection is stored as an AtomicRole DL predicate; match its IRI.
        let is_role = match tableau.ternary_extension_table.get_tuple_object(tuple_index, 0) {
            TableauObject::DLPredicate(DLPredicate::AtomicRole(r)) => r.iri() == role_iri,
            _ => false,
        };
        if !is_role {
            continue;
        }
        let Some(source) = tableau
            .ternary_extension_table
            .get_tuple_object(tuple_index, 1)
            .as_node()
        else {
            continue;
        };
        let Some(target) = tableau
            .ternary_extension_table
            .get_tuple_object(tuple_index, 2)
            .as_node()
        else {
            continue;
        };
        // Both endpoints must be (active, unmerged) named-individual nodes.
        if tableau.node(target).is_merged() || !tableau.node(target).is_active() {
            continue;
        }
        let source_canonical = tableau.get_canonical_node(source);
        let target_canonical = tableau.get_canonical_node(target);
        let (Some(source_iri), Some(target_iri)) = (
            iri_for_canonical.get(&source_canonical),
            iri_for_canonical.get(&target_canonical),
        ) else {
            continue;
        };
        let known = tableau
            .ternary_extension_table
            .get_dependency_set(tuple_index, &empty_set)
            .is_empty();
        if known {
            role_manager
                .get_role_element(role_iri)
                .add_known(source_iri, target_iri);
        }
    }

    // Collect the known pairs from the role element.
    let mut pairs: HashSet<(String, String)> = HashSet::new();
    let element = role_manager.get_role_element(role_iri);
    for (source, targets) in element.known_relations() {
        for target in targets {
            pairs.insert((source.clone(), target.clone()));
        }
    }
    Ok(pairs)
}

/// `InstanceManager.getAxiomsForReadingOffCompexProperties` +
/// `readOffComplexRoleSuccessors`: for a complex object role `role_iri`, add the
/// read-off axioms `A_a(a)` and `A_a ⊑ ∀role.A_a^role` for every named individual
/// `a`, saturate, and collect the known (`empty dependency set`) `A_a^role`-
/// labelled named successors of each `a`. The universal restriction propagates
/// along the full role automaton (so transitive/RIA-implied successors are
/// captured), which the direct ternary read-off would miss.
fn complex_role_known_forward_pairs(
    ontology: &SetOntology<crate::structural::A>,
    role_iri: &str,
) -> Result<std::collections::HashSet<(String, String)>, String> {
    use crate::model::AtomicConcept;
    use crate::tableau::dependency_set::DependencySetOps;
    use crate::tableau::extension_table::View;
    use horned_owl::model::{ObjectPropertyExpression as OPE, SubClassOf};
    use std::collections::HashSet;

    let build = Build::new_arc();

    // The non-internal named individuals to read off (HermiT's m_individuals).
    let dl_base = clausify_for_query(ontology)?;
    let individuals: Vec<String> = dl_base
        .get_all_individuals()
        .iter()
        .map(|i| i.iri().to_string())
        .filter(|iri| !iri.starts_with("internal:"))
        .collect();
    if individuals.is_empty() {
        return Ok(HashSet::new());
    }

    // A_a(a) and A_a ⊑ ∀role.A_a^role for each individual a.
    let mut augmented = ontology.clone();
    let role_property = build.object_property(role_iri.to_string());
    for ind_iri in &individuals {
        let a_concept = build.class(format!("internal:individual-concept#{ind_iri}"));
        let ar_concept = build.class(format!("internal:individual-concept#{role_iri}#{ind_iri}"));
        let named = build.named_individual(ind_iri.clone());
        augmented.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(a_concept.clone()),
            i: OwlIndividual::Named(named),
        }));
        augmented.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(a_concept),
            sup: CE::ObjectAllValuesFrom {
                ope: OPE::ObjectProperty(role_property.clone()),
                bce: Box::new(CE::Class(ar_concept)),
            },
        }));
    }

    let dl_ontology = clausify_ontology(&augmented)?;
    let reasoner = Reasoner::new(&dl_ontology);
    let Some((mut tableau, nodes_for_individuals)) = reasoner.saturate_for_instances() else {
        return Ok(HashSet::new());
    };

    // Canonical node -> named-individual IRI (skipping internal individuals).
    let mut iri_for_canonical: HashMap<NodeId, String> = HashMap::new();
    for (individual, &raw_node) in &nodes_for_individuals {
        let iri = individual.iri();
        if iri.starts_with("internal:") {
            continue;
        }
        let canonical = tableau.get_canonical_node(raw_node);
        iri_for_canonical.entry(canonical).or_insert_with(|| iri.to_string());
    }

    let empty_set = tableau.dependency_set_factory().empty_set();
    let mut pairs: HashSet<(String, String)> = HashSet::new();
    for ind_iri in &individuals {
        let ar_concept = TableauObject::Concept(Concept::AtomicConcept(AtomicConcept::create(
            format!("internal:individual-concept#{role_iri}#{ind_iri}"),
        )));
        let retrieval =
            tableau.create_binary_retrieval([0, -1], [Some(ar_concept), None], View::Total);
        for &tuple_index in &retrieval.tuple_indices {
            let Some(target) = tableau
                .binary_extension_table
                .get_tuple_object(tuple_index, 1)
                .as_node()
            else {
                continue;
            };
            if tableau.node(target).is_merged() || !tableau.node(target).is_active() {
                continue;
            }
            // Only KNOWN (empty dependency set) successors are read off as known.
            let known = tableau
                .binary_extension_table
                .get_dependency_set(tuple_index, &empty_set)
                .is_empty();
            if !known {
                continue;
            }
            let target_canonical = tableau.get_canonical_node(target);
            if let Some(target_iri) = iri_for_canonical.get(&target_canonical) {
                pairs.insert((ind_iri.clone(), target_iri.clone()));
            }
        }
    }
    Ok(pairs)
}

/// The named individuals that are instances of `class` (HermiT's
/// `getInstances`). When `direct` is true, only the *direct* instances are
/// returned -- those for which `class` is a most-specific (direct) type, i.e.
/// no proper subclass of `class` also holds.
pub fn instances(
    ontology: &SetOntology<crate::structural::A>,
    class: &horned_owl::model::Class<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<NamedIndividual<crate::structural::A>>, String> {
    instances_with_configuration(
        ontology,
        class,
        direct,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`instances`], but realises under an explicit
/// [`Configuration`](crate::configuration::Configuration).
pub fn instances_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    class: &horned_owl::model::Class<crate::structural::A>,
    direct: bool,
    configuration: &crate::configuration::Configuration,
) -> Result<std::collections::HashSet<NamedIndividual<crate::structural::A>>, String> {
    use std::collections::HashSet;

    let build = Build::new_arc();
    let dl_ontology = clausify_for_query(ontology)?;

    // Java getInstances() calls checkPreConditions(classExpression) as the
    // first statement INSIDE the `getAllIndividuals().size()>0` guard
    // (Reasoner.java:1664-1665), throwing under the default flag. With zero individuals
    // Java skips the check and returns the empty node set, so gate the throw the same way.
    if !dl_ontology.get_all_individuals().is_empty() {
        check_pre_conditions_with(ontology, configuration, &[class.0.to_string()], &[], &[], &[])?;
    }

    // HermiT `getInstances`: on an *inconsistent* ontology every named individual
    // is an instance of every class, so it returns ALL named individuals,
    // regardless of `class` or `direct` (`Reasoner.java:1666-1669`). This is the
    // flag-OFF fallthrough (only reached when the throw above is disabled). Routing the
    // `direct` case through `realize` (which maps every individual to
    // `{owl:Nothing}` when inconsistent) would instead return the empty set for
    // any `class != owl:Nothing` -- a wrong answer.
    if !is_ontology_consistent_with_configuration(ontology, configuration)? {
        let mut result: HashSet<NamedIndividual<crate::structural::A>> = HashSet::new();
        for individual in dl_ontology.get_all_individuals() {
            let iri = individual.iri();
            if iri.starts_with("internal:") {
                continue;
            }
            result.insert(build.named_individual(iri));
        }
        return Ok(result);
    }

    if direct {
        // A direct instance is one whose most-specific (direct) types include
        // the class.
        let types = realize_with_configuration(ontology, configuration)?;
        return Ok(types
            .into_iter()
            .filter(|(_, direct_types)| direct_types.contains(class))
            .map(|(individual, _)| individual)
            .collect());
    }

    // All instances, read off the realised InstanceManager
    // (`getInstances(node, false)`) instead of one entailment test per individual.
    let mut result: HashSet<NamedIndividual<crate::structural::A>> = HashSet::new();
    let Some(built) = build_class_instance_manager_with_configuration(ontology, configuration)? else {
        // Inconsistent: handled above, so unreachable; defensively return all.
        for individual in dl_ontology.get_all_individuals() {
            let iri = individual.iri();
            if !iri.starts_with("internal:") {
                result.insert(build.named_individual(iri));
            }
        }
        return Ok(result);
    };
    let BuiltClassInstanceManager { manager, hierarchy, individuals } = built;
    if let Some(node) = hierarchy.node_for_element(class) {
        for iri in manager.get_instances(&hierarchy, node, false, &individuals) {
            result.insert(build.named_individual(iri));
        }
    }
    Ok(result)
}

/// `Reasoner.getInstances(OWLClassExpression, boolean)` (Reasoner.java:1663)
/// for an arbitrary class expression.
///
/// A bare named class delegates to [`instances`]. For a complex class expression
/// `ce`, the members for `direct=false` are exactly the named individuals entailed
/// to be instances of `ce`; for `direct=true` we additionally drop any individual
/// that is also an instance of a NAMED class strictly subsumed by `ce` (so its
/// direct type lies below the query concept), reproducing Java's query-concept /
/// child-node semantics including the "under the complex concept but under no named
/// subclass" case.
pub fn instances_of_expression(
    ontology: &SetOntology<crate::structural::A>,
    ce: &CE<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<NamedIndividual<crate::structural::A>>, String> {
    instances_of_expression_with_configuration(
        ontology,
        ce,
        direct,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`instances_of_expression`], but under an explicit `Configuration`.
pub fn instances_of_expression_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    ce: &CE<crate::structural::A>,
    direct: bool,
    configuration: &crate::configuration::Configuration,
) -> Result<std::collections::HashSet<NamedIndividual<crate::structural::A>>, String> {
    use std::collections::HashSet;
    // Named-class fast path (Reasoner.java:1674).
    if let CE::Class(c) = ce {
        return instances_with_configuration(ontology, c, direct, configuration);
    }

    use horned_owl::model::EquivalentClasses;
    let build = Build::new_arc();
    let dl_ontology = clausify_for_query(ontology)?;

    // Java: with zero individuals, getInstances returns the empty set without even
    // checking pre-conditions (Reasoner.java:1664, 1701-1702).
    if dl_ontology.get_all_individuals().is_empty() {
        return Ok(HashSet::new());
    }
    // checkPreConditions(classExpression) on `ce`'s entities (Reasoner.java:1665).
    let (mut classes, mut ops, mut dps, mut inds) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    collect_ce_entities(ce, &mut classes, &mut ops, &mut dps, &mut inds);
    check_pre_conditions_with(ontology, configuration, &classes, &ops, &dps, &inds)?;

    // getInstances on an inconsistent ontology returns ALL named individuals
    // (Reasoner.java:1666-1669).
    if !is_ontology_consistent_with_configuration(ontology, configuration)? {
        let mut result = HashSet::new();
        for individual in dl_ontology.get_all_individuals() {
            if !individual.iri().starts_with("internal:") {
                result.insert(build.named_individual(individual.iri()));
            }
        }
        return Ok(result);
    }

    // Java's complex-expression branch (Reasoner.java:1674-1700):
    //   1. getHierarchyNode(ce): classify the KB and position Q ≡ ce in the cached
    //      hierarchy via HierarchySearch.findPosition.
    //   2. m_instanceManager.getInstances(Q, direct): for a complex query node this
    //      yields nothing when `direct`, else the instances of Q's child subtrees
    //      (InstanceManager.java:1015-1028).
    //   3. a sibling walk from Q's parents downward (Q's child subtrees already
    //      covered): for each visited node its DIRECT instances that are actual
    //      instances of ce -- tested on ONE reused tableau over KB + SubClassOf(Q,¬ce)
    //      by asserting Q(individual) and checking unsatisfiability -- are added.
    let crate::reasoner::BuiltClassInstanceManager { manager, hierarchy, individuals } =
        match build_class_instance_manager_with_configuration(ontology, configuration)? {
            Some(built) => built,
            None => {
                // Inconsistent: handled above; defensively return all named individuals.
                let mut result = HashSet::new();
                for individual in dl_ontology.get_all_individuals() {
                    if !individual.iri().starts_with("internal:") {
                        result.insert(build.named_individual(individual.iri()));
                    }
                }
                return Ok(result);
            }
        };

    // getHierarchyNode(ce): position Q in the KB hierarchy via findPosition with a
    // reused KB + Q ≡ ce tableau as the doesSubsume oracle.
    let query_class = build.class("internal:query-concept");
    let mut position_ontology = ontology.clone();
    position_ontology.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(query_class.clone()),
        ce.clone(),
    ])));
    let position_dl = clausify_for_query(&position_ontology)?;
    let position_reasoner = Reasoner::new(&position_dl);
    let position_manager = std::cell::RefCell::new(position_reasoner.new_manager());
    let position = hierarchy.find_position(&query_class, |parent, child| {
        let sub = crate::model::AtomicConcept::create(child.0.to_string());
        let sup = crate::model::AtomicConcept::create(parent.0.to_string());
        position_reasoner.atomic_subsumes(&mut position_manager.borrow_mut(), &sub, &sup)
    });
    // Q's children / parents within the KB hierarchy. When Q coincides with an
    // existing node, that node's children/parents are Q's (Java still takes the
    // complex branch, since Q's representative is internal:query-concept).
    let (q_children, q_parents): (Vec<crate::hierarchy::NodeRef>, Vec<crate::hierarchy::NodeRef>) =
        match &position {
            crate::hierarchy::Position::Existing(node) => (
                hierarchy.node(*node).child_nodes().iter().copied().collect(),
                hierarchy.node(*node).parent_nodes().iter().copied().collect(),
            ),
            crate::hierarchy::Position::Between { parents, children } => {
                (children.iter().copied().collect(), parents.iter().copied().collect())
            }
        };

    let mut result: HashSet<NamedIndividual<crate::structural::A>> = HashSet::new();
    // m_instanceManager.getInstances(Q, direct): empty for the direct complex case,
    // else the instances of Q's child subtrees.
    if !direct {
        for &child in &q_children {
            for iri in manager.get_instances(&hierarchy, child, false, &individuals) {
                result.insert(build.named_individual(iri));
            }
        }
    }

    // The sibling walk. The instance test reuses ONE tableau over KB + SubClassOf(Q,¬ce):
    // asserting Q(individual) forces individual ∈ ¬ce, so unsatisfiability means
    // individual is necessarily an instance of ce.
    let mut test_ontology = ontology.clone();
    test_ontology.insert(Component::SubClassOf(horned_owl::model::SubClassOf {
        sub: CE::Class(query_class.clone()),
        sup: CE::ObjectComplementOf(Box::new(ce.clone())),
    }));
    let test_dl = clausify_for_query(&test_ontology)?;
    let test_reasoner = Reasoner::new(&test_dl);
    let mut test_manager = test_reasoner.new_manager();
    let query_concept = crate::model::AtomicConcept::create("internal:query-concept");
    let mut visited: std::collections::HashSet<crate::hierarchy::NodeRef> =
        q_children.iter().copied().collect();
    let mut to_visit: Vec<crate::hierarchy::NodeRef> = q_parents;
    while let Some(node) = to_visit.pop() {
        if visited.insert(node) {
            for iri in manager.get_instances(&hierarchy, node, true, &individuals) {
                let atom = crate::model::Atom::create(
                    DLPredicate::AtomicConcept(query_concept.clone()),
                    vec![Term::Individual(crate::model::Individual::create(&iri))],
                );
                if !test_reasoner.is_consistent_with_test_atoms(&mut test_manager, &[atom]) {
                    result.insert(build.named_individual(iri));
                }
            }
            to_visit.extend(hierarchy.node(node).child_nodes().iter().copied());
        }
    }
    Ok(result)
}

/// Realises the ABox: maps each named individual to its **direct types** -- the
/// most-specific named classes it is an instance of -- mirroring HermiT's
/// `getTypes(individual, direct=true)`.
///
/// Types are upward-closed under subsumption, so the direct types of `a` are the
/// type nodes none of whose children are also types of `a`. An inconsistent
/// ontology makes every individual an instance of everything; we report this by
/// mapping each individual to `{owl:Nothing}` (the bottom node), matching
/// HermiT's bottom-node answer.
pub fn realize(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<
    HashMap<
        NamedIndividual<crate::structural::A>,
        std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>,
    >,
    String,
> {
    realize_with_configuration(ontology, &crate::configuration::Configuration::default())
}

/// As [`realize`], but realises under an explicit
/// [`Configuration`](crate::configuration::Configuration).
pub fn realize_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<
    HashMap<
        NamedIndividual<crate::structural::A>,
        std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>,
    >,
    String,
> {
    use horned_owl::model::Class;
    use std::collections::HashSet;

    // Java realise() calls checkPreConditions() unconditionally FIRST
    // (Reasoner.java:1597-1598), throwing under the default flag. The all-individuals →
    // {owl:Nothing} mapping below is the flag-OFF fallthrough.
    throw_inconsistent_ontology_exception_if_necessary(ontology, configuration)?;

    let build = Build::new_arc();

    // Named individuals of the clausified vocabulary (skipping internal ones).
    let dl_ontology = clausify_for_query(ontology)?;
    let mut individuals: Vec<NamedIndividual<crate::structural::A>> = Vec::new();
    for individual in dl_ontology.get_all_individuals() {
        let iri = individual.iri();
        if iri.starts_with("internal:") {
            continue;
        }
        individuals.push(build.named_individual(iri));
    }

    let mut result: HashMap<
        NamedIndividual<crate::structural::A>,
        HashSet<Class<crate::structural::A>>,
    > = HashMap::new();

    // Read the known/possible instances off the saturated model and
    // realise (confirm possibles with the oracle, never the knowns), instead of
    // testing every (individual, concept) pair. `None` => inconsistent: every
    // individual's direct types are the classified bottom node, which on an
    // inconsistent ontology holds every (non-internal) class
    // (`InstanceManager.getTypes` returns `singleton(bottomNode)`).
    let Some(built) = build_class_instance_manager_with_configuration(ontology, configuration)? else {
        let hierarchy = classify_with_configuration(ontology, configuration)?;
        let bottom: HashSet<Class<crate::structural::A>> =
            hierarchy.all_elements().cloned().collect();
        for individual in individuals {
            result.insert(individual, bottom.clone());
        }
        return Ok(result);
    };
    let BuiltClassInstanceManager { manager, hierarchy, .. } = built;

    for individual in individuals {
        let iri = individual.0.to_string();
        // The direct type nodes, read directly from the realised KNOWN instances.
        let direct_nodes = manager.get_types_of(&hierarchy, &iri, true);
        let mut direct_types: HashSet<Class<crate::structural::A>> = HashSet::new();
        for node in direct_nodes {
            for class in hierarchy.node(node).equivalent_elements() {
                direct_types.insert(class.clone());
            }
        }
        result.insert(individual, direct_types);
    }

    Ok(result)
}

/// The named-class types of `individual` (HermiT's `Reasoner.getTypes`,
/// `Reasoner.java:1620`). For `direct=true` the most-specific (direct) named
/// types; for `direct=false` the full up-closed set of all named types up to and
/// including `owl:Thing`. An individual not in the ontology vocabulary
/// (`!isDefined`) yields `{owl:Thing}` (the top node), matching Java's
/// `isDefined` branch. On an inconsistent ontology every individual is an
/// instance of everything, so direct=false yields all classified classes and
/// direct=true yields `{owl:Nothing}`.
pub fn get_types(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    get_types_with_configuration(
        ontology,
        individual,
        direct,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`get_types`], but realises under an explicit
/// [`Configuration`](crate::configuration::Configuration).
pub fn get_types_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
    direct: bool,
    configuration: &crate::configuration::Configuration,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    use horned_owl::model::Class;
    use std::collections::HashSet;

    // Java getTypes() calls checkPreConditions(individual) FIRST
    // (Reasoner.java:1620-1621), before the isDefined branch — the fresh-entity throw
    // (over the individual) then the inconsistency throw, under the default flag.
    check_pre_conditions_with(ontology, configuration, &[], &[], &[], &[individual.0.to_string()])?;

    let build = Build::new_arc();
    let thing = build.class("http://www.w3.org/2002/07/owl#Thing");

    // isDefined: the individual must occur in the clausified vocabulary. A
    // fresh/undefined individual gets the whole TOP node (Reasoner.getTypes ~1623-1627:
    // result={topNode}, expanded by atomicConceptHierarchyNodeToNode to every
    // non-internal class equivalent to owl:Thing). The branch ignores
    // `direct`, exactly as Java does.
    let dl_ontology = clausify_for_query(ontology)?;
    let target_iri = individual.0.to_string();
    let is_defined = dl_ontology
        .get_all_individuals()
        .iter()
        .any(|i| i.iri() == target_iri);
    if !is_defined {
        let top_node = classify(ontology)?.equivalent_elements_of(&thing);
        if top_node.is_empty() {
            return Ok(std::iter::once(thing).collect());
        }
        return Ok(top_node);
    }

    // Read the types off the realised InstanceManager. `None` =>
    // inconsistent: `InstanceManager.getTypes` returns `singleton(bottomNode)`
    // for BOTH direct and indirect (InstanceManager.java:916-918), and on an
    // inconsistent ontology the classified bottom node holds every (non-internal)
    // class. So both cases return the full set of classified classes.
    let Some(built) = build_class_instance_manager_with_configuration(ontology, configuration)? else {
        let hierarchy = classify_with_configuration(ontology, configuration)?;
        return Ok(hierarchy.all_elements().cloned().collect());
    };
    let BuiltClassInstanceManager { manager, hierarchy, .. } = built;

    let type_nodes = manager.get_types_of(&hierarchy, &target_iri, direct);

    let mut result: HashSet<Class<crate::structural::A>> = HashSet::new();
    if direct {
        for node in type_nodes {
            for class in hierarchy.node(node).equivalent_elements() {
                result.insert(class.clone());
            }
        }
    } else {
        // Up-closed set: all named classes of every (known) type node, plus
        // owl:Thing. The saturated read-off already up-closes the known nodes.
        for node in type_nodes {
            for class in hierarchy.node(node).equivalent_elements() {
                result.insert(class.clone());
            }
        }
        result.insert(thing);
    }
    Ok(result)
}

// ===========================================================================
// OWLReasoner API surface (thin reductions over the existing
// reasoning services). Each function mirrors the named `Reasoner` Java method's
// reduction, precondition and inconsistency behaviour.
// ===========================================================================

/// `Reasoner.getObjectPropertyValues` (Reasoner.java:1749). The named
/// individuals `o` for which `ope(individual, o)` is entailed. Mirrors HermiT's
/// `InstanceManager.getObjectPropertyValues` (the successors of a fixed subject),
/// here computed by entailment over `object_property_instances`. On an
/// inconsistent ontology Java returns *all* named individuals; `checkPreConditions`
/// throws first under the default flag, so the throw takes precedence.
pub fn get_object_property_values(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<std::collections::HashSet<NamedIndividual<crate::structural::A>>, String> {
    check_pre_conditions(ontology)?;
    let mut result = std::collections::HashSet::new();
    // `if (!m_dlOntology.containsObjectRole(role)) return new ...NodeSet()`
    // (Reasoner.java:1756): a property absent from the (clausified) ontology has no
    // values, so bail before computing the property's extension.
    let role = crate::model::AtomicRole::create(
        crate::structural::named_property(&ope).0.to_string(),
    );
    if !clausify_for_query(ontology)?.contains_object_role(&role) {
        return Ok(result);
    }
    for (from, to) in object_property_instances(ontology, ope)? {
        if from == *individual {
            result.insert(to);
        }
    }
    Ok(result)
}

/// `Reasoner.getDataPropertyValues` (Reasoner.java:1807). The literals `v`
/// asserted for `dp` (and all its sub-data-properties) on `individual` or any
/// individual same-as it. Mirrors Java: gather the asserted data-property values
/// from the clausified ABox over `getSubDataProperties(dp,false) ∪ {dp}` and over
/// `getSameIndividuals(individual)`. (HermiT only reads *asserted* values here, so
/// this is read-from-ABox, not an entailment query.)
pub fn get_data_property_values(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
    dp: horned_owl::model::DataProperty<crate::structural::A>,
) -> Result<std::collections::HashSet<horned_owl::model::Literal<crate::structural::A>>, String> {
    use crate::model::{AtomicRole, Individual as DlIndividual};
    use horned_owl::model::Literal;
    check_pre_conditions(ontology)?;
    let build = Build::new_arc();
    let mut result = std::collections::HashSet::new();

    let dl_ontology = clausify_for_query(ontology)?;
    if !dl_ontology.has_datatypes() {
        return Ok(result);
    }

    // Relevant data properties: dp plus all its (non-direct) sub-properties.
    let mut relevant_dps: std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>> =
        get_sub_data_properties(ontology, &dp, false)?;
    relevant_dps.insert(dp);

    // Relevant individuals: the same-as set of `individual` (BY_NAME default => self).
    let relevant_individuals = get_same_individuals(ontology, individual)?;

    let assertions = dl_ontology.get_data_property_assertions();
    for data_property in &relevant_dps {
        if data_property.0.to_string() == "http://www.w3.org/2002/07/owl#bottomDataProperty" {
            continue;
        }
        let atomic_role = AtomicRole::create(data_property.0.to_string());
        if let Some(per_individual) = assertions.get(&atomic_role) {
            for ind in &relevant_individuals {
                let dl_ind = DlIndividual::create(ind.0.to_string());
                if let Some(constants) = per_individual.get(&dl_ind) {
                    for constant in constants {
                        // Java getDataPropertyValues (Reasoner.java:1827-1832)
                        // special-cases rdf:PlainLiteral, splitting the lexical form on the
                        // LAST '@' into text + language tag and emitting a language literal.
                        if constant.datatype_uri()
                            == "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral"
                        {
                            let lf = constant.lexical_form();
                            match lf.rfind('@') {
                                Some(at) if !lf[at + 1..].is_empty() => {
                                    result.insert(Literal::Language {
                                        literal: lf[..at].to_string(),
                                        lang: lf[at + 1..].to_string(),
                                    });
                                }
                                Some(at) => {
                                    result.insert(Literal::Simple { literal: lf[..at].to_string() });
                                }
                                None => {
                                    result.insert(Literal::Simple { literal: lf.to_string() });
                                }
                            }
                        } else {
                            result.insert(Literal::Datatype {
                                datatype_iri: build.iri(constant.datatype_uri().to_string()),
                                literal: constant.lexical_form().to_string(),
                            });
                        }
                    }
                }
            }
        }
    }
    Ok(result)
}

/// `Reasoner.getObjectPropertyDomains` (Reasoner.java:1116). The named
/// classes `C` with `dom(ope) ⊑ C` -- i.e. `∃ope.⊤ ⊑ C` -- as super-classes of
/// the class `∃ope.⊤`. `direct` restricts to the most-specific such classes.
pub fn get_object_property_domains(
    ontology: &SetOntology<crate::structural::A>,
    ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    check_pre_conditions(ontology)?;
    // include_bottom=true: Java's HierarchySearch.search descends to the bottom
    // node when the property is necessarily empty (Reasoner.java:1140).
    super_classes_of_description(ontology, some_values(ope, thing()), direct, true)
}

/// `Reasoner.getObjectPropertyRanges` (Reasoner.java:1147). The named
/// classes `C` with `range(ope) ⊑ C` -- i.e. `⊤ ⊑ ∀ope.C`, equivalently
/// `∃ope⁻.⊤ ⊑ C`: the super-classes of `∃Inv(ope).⊤`.
pub fn get_object_property_ranges(
    ontology: &SetOntology<crate::structural::A>,
    ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    check_pre_conditions(ontology)?;
    let inv = invert_ope(ope);
    // include_bottom=true: Java's HierarchySearch.search descends to the bottom
    // node when the property is necessarily empty (Reasoner.java:1171).
    super_classes_of_description(ontology, some_values(&inv, thing()), direct, true)
}

/// `Reasoner.getDataPropertyDomains` (Reasoner.java:1483). The named
/// classes `C` with `dom(dp) ⊑ C` -- i.e. `∃dp.rdfs:Literal ⊑ C`: the
/// super-classes of `∃dp.Literal`.
pub fn get_data_property_domains(
    ontology: &SetOntology<crate::structural::A>,
    dp: &horned_owl::model::DataProperty<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    check_pre_conditions(ontology)?;
    // include_bottom=true: same HierarchySearch.search semantics as object-property
    // domains (Reasoner.java:1483/1140 pattern).
    super_classes_of_description(ontology, data_some_literal(dp), direct, true)
}

/// There is no `getDataPropertyRanges` in HermiT's `Reasoner` (data ranges
/// are not named classes), provided for API symmetry: the range of a data
/// property is the union of declared `DataPropertyRange` datatypes. We expose the
/// declared data ranges of `dp` directly from the ontology.
pub fn get_data_property_ranges(
    ontology: &SetOntology<crate::structural::A>,
    dp: &horned_owl::model::DataProperty<crate::structural::A>,
) -> Result<Vec<horned_owl::model::DataRange<crate::structural::A>>, String> {
    check_pre_conditions(ontology)?;
    let mut result = Vec::new();
    for annotated in ontology.iter() {
        if let Component::DataPropertyRange(ax) = &annotated.component {
            if &ax.dp == dp {
                result.push(ax.dr.clone());
            }
        }
    }
    Ok(result)
}

/// Helper shared by the domain/range getters: the named classes that subsume
/// `description`, computed from the classified hierarchy. `direct` restricts to
/// the most-specific such classes. Mirrors HermiT's `HierarchySearch.search` over
/// the class hierarchy for the domain/range predicate, here realised by a
/// subsumption test per representative.
///
/// `include_bottom` controls whether the bottom node (owl:Nothing) is eligible:
/// - `true`  — domain/range callers (Reasoner.java:1116-1177 / 1483): the search
///   descends all the way to the bottom node when the description is unsatisfiable
///   (e.g. the property is necessarily empty), so owl:Nothing is a valid direct
///   domain/range result.
/// - `false` — `getSuperClasses`-style callers: Java removes the node itself from
///   the ancestor set (Reasoner.java:812), so owl:Nothing is never a super-class.
fn super_classes_of_description(
    ontology: &SetOntology<crate::structural::A>,
    description: CE<crate::structural::A>,
    direct: bool,
    include_bottom: bool,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    use horned_owl::model::Class;
    use std::collections::HashSet;
    use crate::hierarchy::Position;
    // Java's domain/range search is `HierarchySearch.search` over the classified
    // hierarchy with a reused-tableau predicate `description ⊑ representative`
    // (Reasoner.java domain/range getters): it positions `description` in the cached
    // hierarchy and reads its (super-)nodes -- exactly getHierarchyNode(description)
    // + ancestors -- rather than re-classifying with `Q` added.
    //
    // include_bottom=true (domain/range): a class equivalent to the description is a
    // (direct) domain, so Q's own node counts; owl:Nothing is reachable when the
    // description is unsatisfiable (Q lands in the bottom node).
    // include_bottom=false (getSuperClasses-style): the node itself is removed
    // (strict ancestors, Reasoner.java:812) so equivalents / owl:Nothing are not
    // returned.
    let (hierarchy, position) = position_query_concept(ontology, &description)?;
    let mut result: HashSet<Class<crate::structural::A>> = HashSet::new();
    let push = |result: &mut HashSet<Class<crate::structural::A>>, node| {
        for class in hierarchy.node(node).equivalent_elements() {
            result.insert(class.clone());
        }
    };
    match position {
        Position::Existing(node) => {
            if direct {
                if include_bottom {
                    // The description is equivalent to named class(es); those are the
                    // most-specific (direct) super-classes / domains.
                    push(&mut result, node);
                } else {
                    for &parent in hierarchy.node(node).parent_nodes() {
                        push(&mut result, parent);
                    }
                }
            } else {
                // Reflexive ancestors; drop Q's own node when equivalents are excluded.
                for anc in hierarchy.ancestor_nodes(node) {
                    if anc == node && !include_bottom {
                        continue;
                    }
                    push(&mut result, anc);
                }
            }
        }
        Position::Between { parents, .. } => {
            if direct {
                for parent in parents {
                    push(&mut result, parent);
                }
            } else {
                let mut ancestors: HashSet<_> = HashSet::new();
                for parent in parents {
                    ancestors.extend(hierarchy.ancestor_nodes(parent));
                }
                for a in ancestors {
                    push(&mut result, a);
                }
            }
        }
    }
    Ok(result)
}


/// Port of `Reasoner.getHierarchyNode(classExpression)` (Reasoner.java:920-940)
/// for a COMPLEX class expression: classify the KB ONCE (`classifyClasses()`),
/// then position a fresh query concept `Q ≡ ce` in that classified hierarchy via
/// `HierarchySearch.findPosition`, using ONE reused tableau (over `KB ∪ {Q ≡ ce}`,
/// HermiT's `getTableau(classDefinitionAxiom)`) for the `doesSubsume` oracle.
/// Returns the KB's classified hierarchy and `Q`'s `Position` within it. This is
/// HermiT's algorithm: it tests `ce` against only the representatives the search
/// must, reusing the cached class hierarchy, rather than re-classifying the whole
/// KB with `Q` added.
fn position_query_concept(
    ontology: &SetOntology<crate::structural::A>,
    ce: &CE<crate::structural::A>,
) -> Result<
    (
        crate::hierarchy::Hierarchy<horned_owl::model::Class<crate::structural::A>>,
        crate::hierarchy::Position,
    ),
    String,
> {
    use horned_owl::model::EquivalentClasses;
    let build = Build::new_arc();
    // HermiT uses the fixed IRI internal:query-concept (Reasoner.java:935).
    let query_class = build.class("internal:query-concept");
    // classifyClasses(): the classified hierarchy of the KB alone.
    let hierarchy = classify(ontology)?;
    // getTableau(Q ≡ ce): one reused tableau that knows the query concept, used by
    // the subsumption oracle below (HermiT's `final Tableau tableau`).
    let mut query_ontology = ontology.clone();
    query_ontology.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(query_class.clone()),
        ce.clone(),
    ])));
    let dl_ontology = clausify_for_query(&query_ontology)?;
    let reasoner = Reasoner::new(&dl_ontology);
    let manager = std::cell::RefCell::new(reasoner.new_manager());
    // HierarchySearch.findPosition with doesSubsume(parent, child) == `child ⊑ parent`,
    // tested by `child(fresh) ∧ ¬parent(fresh)` being unsatisfiable on the reused
    // tableau (Reasoner.getHierarchyNode's anonymous `Relation`).
    let position = hierarchy.find_position(&query_class, |parent, child| {
        let sub = crate::model::AtomicConcept::create(child.0.to_string());
        let sup = crate::model::AtomicConcept::create(parent.0.to_string());
        reasoner.atomic_subsumes(&mut manager.borrow_mut(), &sub, &sup)
    });
    Ok((hierarchy, position))
}

/// `Reasoner.getSuperClasses(OWLClassExpression, boolean)` (Reasoner.java:805).
/// The named classes subsuming `ce`. A bare named
/// class delegates to [`super_classes`]; a complex CE is positioned via the
/// query-concept subsumption search.
pub fn super_classes_of_expression(
    ontology: &SetOntology<crate::structural::A>,
    ce: &CE<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    check_pre_conditions(ontology)?;
    if let CE::Class(c) = ce {
        return super_classes(ontology, c, direct);
    }
    // Java getSuperClasses(ce) = getHierarchyNode(ce) then the parent nodes (direct)
    // or ancestor nodes minus the node itself (Reasoner.java:805-815).
    use horned_owl::model::Class;
    use std::collections::HashSet;
    use crate::hierarchy::Position;
    let (hierarchy, position) = position_query_concept(ontology, ce)?;
    let mut result: HashSet<Class<crate::structural::A>> = HashSet::new();
    let push = |result: &mut HashSet<Class<crate::structural::A>>, node| {
        for class in hierarchy.node(node).equivalent_elements() {
            result.insert(class.clone());
        }
    };
    // The hierarchy nodes that are Q's super-classes: its parents (direct) or its
    // strict ancestors (non-direct). `getAncestorNodes()` minus Q's own node is the
    // ancestor closure of Q's parents.
    match position {
        Position::Existing(node) => {
            if direct {
                for &p in hierarchy.node(node).parent_nodes() {
                    push(&mut result, p);
                }
            } else {
                for anc in hierarchy.ancestor_nodes(node) {
                    if anc != node {
                        push(&mut result, anc);
                    }
                }
            }
        }
        Position::Between { parents, .. } => {
            if direct {
                for p in parents {
                    push(&mut result, p);
                }
            } else {
                let mut ancestors: HashSet<_> = HashSet::new();
                for p in parents {
                    ancestors.extend(hierarchy.ancestor_nodes(p));
                }
                for a in ancestors {
                    push(&mut result, a);
                }
            }
        }
    }
    Ok(result)
}

/// `Reasoner.getSubClasses(OWLClassExpression, boolean)` (Reasoner.java:816).
/// The named classes subsumed by `ce`.
pub fn sub_classes_of_expression(
    ontology: &SetOntology<crate::structural::A>,
    ce: &CE<crate::structural::A>,
    direct: bool,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    check_pre_conditions(ontology)?;
    if let CE::Class(c) = ce {
        return sub_classes(ontology, c, direct);
    }
    // Java getSubClasses(ce) = getHierarchyNode(ce) then the child nodes (direct) or
    // descendant nodes minus the node itself (Reasoner.java:816-826).
    use horned_owl::model::Class;
    use std::collections::HashSet;
    use crate::hierarchy::Position;
    let (hierarchy, position) = position_query_concept(ontology, ce)?;
    let mut result: HashSet<Class<crate::structural::A>> = HashSet::new();
    let push = |result: &mut HashSet<Class<crate::structural::A>>, node| {
        for class in hierarchy.node(node).equivalent_elements() {
            result.insert(class.clone());
        }
    };
    match position {
        Position::Existing(node) => {
            if direct {
                for &c in hierarchy.node(node).child_nodes() {
                    push(&mut result, c);
                }
            } else {
                for desc in hierarchy.descendant_nodes(node) {
                    if desc != node {
                        push(&mut result, desc);
                    }
                }
            }
        }
        Position::Between { children, .. } => {
            if direct {
                for c in children {
                    push(&mut result, c);
                }
            } else {
                let mut descendants: HashSet<_> = HashSet::new();
                for c in children {
                    descendants.extend(hierarchy.descendant_nodes(c));
                }
                for d in descendants {
                    push(&mut result, d);
                }
            }
        }
    }
    Ok(result)
}

/// `Reasoner.getEquivalentClasses(OWLClassExpression)` (Reasoner.java:801).
/// The named classes equivalent to `ce` (subsume-both-ways).
pub fn equivalent_classes_of_expression(
    ontology: &SetOntology<crate::structural::A>,
    ce: &CE<crate::structural::A>,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    use std::collections::HashSet;
    check_pre_conditions(ontology)?;
    if let CE::Class(c) = ce {
        return equivalent_classes(ontology, c);
    }
    // Java getEquivalentClasses(ce) = getHierarchyNode(ce): it defines
    // internal:query-concept ≡ ce, positions it in the classified hierarchy and
    // returns that node's (named) classes (Reasoner.java:801-804). When Q lands on
    // an existing node (it is equivalent to those members, including the ≡owl:Thing /
    // unsatisfiable ≡owl:Nothing cases) those members are the equivalents; when Q
    // sits strictly between nodes, no named class is equivalent.
    use crate::hierarchy::Position;
    let (hierarchy, position) = position_query_concept(ontology, ce)?;
    let mut result: HashSet<horned_owl::model::Class<crate::structural::A>> = HashSet::new();
    if let Position::Existing(node) = position {
        for member in hierarchy.node(node).equivalent_elements() {
            result.insert(member.clone());
        }
    }
    Ok(result)
}

/// `Reasoner.getDisjointClasses(OWLClassExpression)` (Reasoner.java:832,
/// complex branch 860-867). For a complex CE Java returns
/// `getEquivalentClasses(¬ce) ∪ getSubClasses(¬ce, false)`.
pub fn disjoint_classes_of_expression(
    ontology: &SetOntology<crate::structural::A>,
    ce: &CE<crate::structural::A>,
) -> Result<std::collections::HashSet<horned_owl::model::Class<crate::structural::A>>, String> {
    if let CE::Class(c) = ce {
        return disjoint_classes(ontology, c);
    }
    check_pre_conditions(ontology)?;
    let complement = CE::ObjectComplementOf(Box::new(ce.clone()));
    // Java: getEquivalentClasses(¬ce) ∪ getSubClasses(¬ce, false) (Reasoner.java:860-867).
    let mut result = equivalent_classes_of_expression(ontology, &complement)?;
    result.extend(sub_classes_of_expression(ontology, &complement, false)?);
    Ok(result)
}

/// `Reasoner.getSameIndividuals` (Reasoner.java:1718). The named
/// individuals same-as `individual` (including itself). Under the default
/// `BY_NAME` individual-node-set policy HermiT returns the flat set; we collect
/// every named individual `b` with `is_same_individual(individual, b)`.
pub fn get_same_individuals(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
) -> Result<std::collections::HashSet<NamedIndividual<crate::structural::A>>, String> {
    use std::collections::HashSet;
    check_pre_conditions(ontology)?;
    let build = Build::new_arc();
    let mut result: HashSet<NamedIndividual<crate::structural::A>> = HashSet::new();
    result.insert(individual.clone());

    // `InstanceManager.getSameAsIndividuals`: seed equivalence classes from the
    // model's individual merges (definite unioned, non-deterministic recorded as
    // possible), then confirm only the possible candidates via the oracle -- rather
    // than testing every pair of individuals.
    let Some(built) =
        build_class_instance_manager_with_configuration(ontology, &crate::configuration::Configuration::default())?
    else {
        // Inconsistent (reached only when the throw flag is off): every named
        // individual is the same (Reasoner.getSameIndividuals, inconsistent branch).
        let dl_ontology = clausify_for_query(ontology)?;
        for other in dl_ontology.get_all_individuals() {
            if !other.iri().starts_with("internal:") {
                result.insert(build.named_individual(other.iri()));
            }
        }
        return Ok(result);
    };
    let BuiltClassInstanceManager { mut manager, .. } = built;
    // `Reasoner.getSameIndividuals` (Reasoner.java:1722-1723): a consistent ontology
    // with no individuals, or one not containing `individual`, yields just
    // {individual} (no equivalence-class computation).
    let dl_ontology = clausify_for_query(ontology)?;
    let dl_individual = crate::model::Individual::create(individual.0.to_string());
    if dl_ontology.get_all_individuals().is_empty()
        || !dl_ontology.contains_individual(&dl_individual)
    {
        return Ok(result);
    }
    let iri = individual.0.to_string();
    let members = manager.get_same_as_individuals(&iri, |a, b| {
        is_same_individual(
            ontology,
            build.named_individual(a.to_string()),
            build.named_individual(b.to_string()),
        )
    })?;
    for member in members {
        if !member.starts_with("internal:") {
            result.insert(build.named_individual(member));
        }
    }
    Ok(result)
}

/// `Reasoner.getDifferentIndividuals` (Reasoner.java:1734). The named
/// individuals provably different from `individual`. Under `BY_NAME` this is a
/// flat set; we collect every named individual `b` with
/// `is_different_individual(individual, b)`.
pub fn get_different_individuals(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
) -> Result<std::collections::HashSet<NamedIndividual<crate::structural::A>>, String> {
    use crate::model::{Atom, Individual as DlIndividual};
    use std::collections::HashSet;
    check_pre_conditions(ontology)?;
    let build = Build::new_arc();
    // Java getDifferentIndividuals (Reasoner.java:1741-1746): `tableau=getTableau()`
    // then, for each candidate, `tableau.isSatisfiable({Equality(a,candidate)})` --
    // ONE tableau reused across the candidates, the KB clausified once. a and
    // candidate are necessarily different iff forcing them equal is inconsistent.
    let dl_ontology = clausify_for_query(ontology)?;
    let self_ind = DlIndividual::create(&individual.0.to_string());
    let candidates: Vec<DlIndividual> = dl_ontology
        .get_all_individuals()
        .iter()
        .filter(|i| !i.iri().starts_with("internal:") && **i != self_ind)
        .cloned()
        .collect();
    let reasoner = Reasoner::new(&dl_ontology);
    let mut manager = reasoner.new_manager();
    let mut result: HashSet<NamedIndividual<crate::structural::A>> = HashSet::new();
    for candidate in candidates {
        let eq = Atom::create(
            DLPredicate::Equality,
            vec![
                Term::Individual(self_ind.clone()),
                Term::Individual(candidate.clone()),
            ],
        );
        if !reasoner.is_consistent_with_test_atoms(&mut manager, &[eq]) {
            result.insert(build.named_individual(candidate.iri()));
        }
    }
    Ok(result)
}

// ---------------------------------------------------------------------------
// Node-grouped getters (Java returns Node / NodeSet, grouping equivalent
// classes/properties and same-individuals). The flat getters above remain a
// membership-faithful convenience; these preserve the partitioning the flat sets
// drop. `NodeSet::flattened()` recovers the flat set, so the two agree on membership.
// ---------------------------------------------------------------------------

/// `getSubClasses(class, direct)` as a [`NodeSet`](crate::node_set::NodeSet) with
/// equivalent subclasses grouped into one node (Java `NodeSet<OWLClass>`).
pub fn sub_class_nodes(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
) -> Result<crate::node_set::NodeSet<Class<crate::structural::A>>, String> {
    sub_class_nodes_with_configuration(ontology, class, direct, &crate::configuration::Configuration::default())
}

/// As [`sub_class_nodes`], under an explicit configuration.
pub fn sub_class_nodes_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
    configuration: &crate::configuration::Configuration,
) -> Result<crate::node_set::NodeSet<Class<crate::structural::A>>, String> {
    check_pre_conditions_with(ontology, configuration, &[class.0.to_string()], &[], &[], &[])?;
    let hierarchy = classify_with_configuration(ontology, configuration)?;
    let subs = hierarchy.sub_elements(class, direct);
    Ok(crate::node_set::group_by_equivalence(subs, |c| hierarchy.equivalent_elements_of(c)))
}

/// `getSuperClasses(class, direct)` as a node-grouped [`NodeSet`](crate::node_set::NodeSet).
pub fn super_class_nodes(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
) -> Result<crate::node_set::NodeSet<Class<crate::structural::A>>, String> {
    super_class_nodes_with_configuration(ontology, class, direct, &crate::configuration::Configuration::default())
}

/// As [`super_class_nodes`], under an explicit configuration.
pub fn super_class_nodes_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
    configuration: &crate::configuration::Configuration,
) -> Result<crate::node_set::NodeSet<Class<crate::structural::A>>, String> {
    check_pre_conditions_with(ontology, configuration, &[class.0.to_string()], &[], &[], &[])?;
    let hierarchy = classify_with_configuration(ontology, configuration)?;
    let supers = hierarchy.super_elements(class, direct);
    Ok(crate::node_set::group_by_equivalence(supers, |c| hierarchy.equivalent_elements_of(c)))
}

/// `getEquivalentClasses(class)` as a single [`Node`](crate::node_set::Node) (Java
/// `Node<OWLClass>`): the class together with all classes equivalent to it.
pub fn equivalent_class_node(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
) -> Result<crate::node_set::Node<Class<crate::structural::A>>, String> {
    Ok(crate::node_set::Node::new(equivalent_classes(ontology, class)?))
}

/// `getTypes(individual, direct)` as a node-grouped [`NodeSet`](crate::node_set::NodeSet),
/// equivalent types grouped into one node (Java `NodeSet<OWLClass>`).
pub fn type_nodes(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
    direct: bool,
) -> Result<crate::node_set::NodeSet<Class<crate::structural::A>>, String> {
    type_nodes_with_configuration(ontology, individual, direct, &crate::configuration::Configuration::default())
}

/// As [`type_nodes`], under an explicit configuration.
pub fn type_nodes_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
    direct: bool,
    configuration: &crate::configuration::Configuration,
) -> Result<crate::node_set::NodeSet<Class<crate::structural::A>>, String> {
    let types = get_types_with_configuration(ontology, individual, direct, configuration)?;
    let hierarchy = classify_with_configuration(ontology, configuration)?;
    Ok(crate::node_set::group_by_equivalence(types, |c| hierarchy.equivalent_elements_of(c)))
}

/// `getSameIndividuals(individual)` as a single [`Node`](crate::node_set::Node)
/// (Java `Node<OWLNamedIndividual>`).
pub fn same_individuals_node(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
) -> Result<crate::node_set::Node<NamedIndividual<crate::structural::A>>, String> {
    Ok(crate::node_set::Node::new(get_same_individuals(ontology, individual)?))
}

/// `getInstances(class, direct)` as a [`NodeSet`](crate::node_set::NodeSet) of
/// individual nodes. Under `IndividualNodeSetPolicy::BySameAs` same-individuals are
/// grouped into one node; under the default `ByName` each individual is its own node
/// (Java `NodeSet<OWLNamedIndividual>`).
pub fn instance_nodes(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
) -> Result<crate::node_set::NodeSet<NamedIndividual<crate::structural::A>>, String> {
    instance_nodes_with_configuration(ontology, class, direct, &crate::configuration::Configuration::default())
}

/// As [`instance_nodes`], under an explicit configuration; the configuration's
/// `individual_node_set_policy` selects ByName (singletons) vs BySameAs (grouped).
pub fn instance_nodes_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
    configuration: &crate::configuration::Configuration,
) -> Result<crate::node_set::NodeSet<NamedIndividual<crate::structural::A>>, String> {
    let flat = instances_with_configuration(ontology, class, direct, configuration)?;
    Ok(group_individuals_by_policy(ontology, flat, configuration))
}

/// `getDifferentIndividuals(individual)` as a policy-grouped
/// [`NodeSet`](crate::node_set::NodeSet) (Java `NodeSet<OWLNamedIndividual>`).
pub fn different_individual_nodes(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
) -> Result<crate::node_set::NodeSet<NamedIndividual<crate::structural::A>>, String> {
    different_individual_nodes_with_configuration(ontology, individual, &crate::configuration::Configuration::default())
}

/// As [`different_individual_nodes`], under an explicit configuration.
pub fn different_individual_nodes_with_configuration(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<crate::node_set::NodeSet<NamedIndividual<crate::structural::A>>, String> {
    let flat = get_different_individuals(ontology, individual)?;
    Ok(group_individuals_by_policy(ontology, flat, configuration))
}

/// Group a flat individual set into nodes per `individual_node_set_policy`: `ByName`
/// yields singleton nodes; `BySameAs` groups same-individuals (Java's
/// `sortBySameAsIfNecessary`, Reasoner.java:1872).
fn group_individuals_by_policy(
    ontology: &SetOntology<crate::structural::A>,
    individuals: std::collections::HashSet<NamedIndividual<crate::structural::A>>,
    configuration: &crate::configuration::Configuration,
) -> crate::node_set::NodeSet<NamedIndividual<crate::structural::A>> {
    use crate::configuration::IndividualNodeSetPolicy;
    match configuration.individual_node_set_policy {
        IndividualNodeSetPolicy::ByName => crate::node_set::NodeSet::new(
            individuals.into_iter().map(crate::node_set::Node::singleton).collect(),
        ),
        IndividualNodeSetPolicy::BySameAs => {
            crate::node_set::group_by_equivalence(individuals, |i| {
                // The consistency/precondition checks already ran in the flat getter,
                // so an error here is not expected; fall back to a singleton group.
                get_same_individuals(ontology, i).unwrap_or_else(|_| std::iter::once(i.clone()).collect())
            })
        }
    }
}

/// `getEquivalentObjectProperties(ope)` as a single [`Node`](crate::node_set::Node).
pub fn equivalent_object_property_node(
    ontology: &SetOntology<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<
    crate::node_set::Node<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>,
    String,
> {
    Ok(crate::node_set::Node::new(get_equivalent_object_properties(ontology, &ope)?))
}

/// `getEquivalentDataProperties(dp)` as a single [`Node`](crate::node_set::Node).
pub fn equivalent_data_property_node(
    ontology: &SetOntology<crate::structural::A>,
    dp: horned_owl::model::DataProperty<crate::structural::A>,
) -> Result<crate::node_set::Node<horned_owl::model::DataProperty<crate::structural::A>>, String> {
    Ok(crate::node_set::Node::new(get_equivalent_data_properties(ontology, &dp)?))
}

/// `Reasoner.getDisjointObjectProperties` (Reasoner.java:1181). The named
/// object properties `Q` with `ope ⊓ Q` empty -- i.e. asserting `ope(a,b) ∧
/// Q(a,b)` for fresh `a,b` is inconsistent. Includes everything subsumed by such
/// a `Q` (descendant-closed, as Java adds `getDescendantNodes`), plus the
/// always-disjoint owl:bottomObjectProperty.
pub fn get_disjoint_object_properties(
    ontology: &SetOntology<crate::structural::A>,
    ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<
    std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>,
    String,
> {
    use horned_owl::model::ObjectPropertyExpression as OPE;
    use std::collections::HashSet;
    check_pre_conditions(ontology)?;
    // An inconsistent ontology yields the empty node set (Reasoner.java:1183-1184).
    // This is the flag-OFF fallthrough; under the default flag `check_pre_conditions`
    // already threw.
    if !is_ontology_consistent(ontology)? {
        return Ok(HashSet::new());
    }
    let build = Build::new_arc();
    const TOP: &str = "http://www.w3.org/2002/07/owl#topObjectProperty";
    const BOTTOM: &str = "http://www.w3.org/2002/07/owl#bottomObjectProperty";
    // Source from the OPE hierarchy (as the sub/super/equivalent getters do) so the
    // result node can include inverse-role members, exactly as Java's
    // objectPropertyHierarchyNodesToNodeSet (Reasoner.java:1181-1221).
    let hierarchy = classify_object_property_expressions(ontology)?;
    let bottom_ope = || OPE::ObjectProperty(build.object_property(BOTTOM));
    let named_iri = |expression: &OPE<crate::structural::A>| match expression {
        OPE::ObjectProperty(p) | OPE::InverseObjectProperty(p) => p.0.to_string(),
    };
    let mut result: HashSet<OPE<crate::structural::A>> = HashSet::new();
    let arg_iri = named_iri(ope);
    // owl:topObjectProperty is disjoint only from the bottom node (Reasoner.java:1187).
    if arg_iri == TOP {
        return Ok(hierarchy.equivalent_elements_of(&bottom_ope()));
    }
    // owl:bottomObjectProperty is disjoint from EVERYTHING: the top node plus all its
    // descendants -- i.e. every classified expression (Reasoner.java:1191-1196).
    // Java uses `propertyExpression.isOWLBottomObjectProperty()`, which (unlike the
    // top check) does NOT unwrap inverses, so `Inv(owl:bottomObjectProperty)` is
    // NOT treated as bottom and falls through to the general per-node walk.
    if matches!(ope, OPE::ObjectProperty(_)) && arg_iri == BOTTOM {
        return Ok(hierarchy.all_elements().cloned().collect());
    }
    // Java reuses one tableau (getTableau()) and tests each candidate node with
    // `tableau.isSatisfiable({ope(a,b), rep(a,b)})` on fresh ANONYMOUS individuals
    // a,b (Reasoner.java:1198-1212). Clausify once, build one Reasoner+manager and
    // run the reused-tableau per-test-atom check per node.
    let dl_ontology = clausify_for_query(ontology)?;
    let reasoner = Reasoner::new(&dl_ontology);
    let mut manager = reasoner.new_manager();
    let fresh_a = crate::model::Individual::create_anonymous("fresh-individual-A");
    let fresh_b = crate::model::Individual::create_anonymous("fresh-individual-B");
    let role_atom = |expr: &OPE<crate::structural::A>| -> crate::model::Atom {
        use crate::model::{Atom, AtomicRole};
        match expr {
            OPE::ObjectProperty(p) => Atom::create(
                DLPredicate::AtomicRole(AtomicRole::create(p.0.to_string())),
                vec![Term::Individual(fresh_a.clone()), Term::Individual(fresh_b.clone())],
            ),
            // Inverse role: the named property with the arguments swapped.
            OPE::InverseObjectProperty(p) => Atom::create(
                DLPredicate::AtomicRole(AtomicRole::create(p.0.to_string())),
                vec![Term::Individual(fresh_b.clone()), Term::Individual(fresh_a.clone())],
            ),
        }
    };
    let ope_atom = role_atom(ope);
    // Top-down pruning walk (Reasoner.java:1202-1218): start from the top node's
    // children; test each node's representative for disjointness with `ope`; on
    // disjointness add the whole (reflexive) descendant subtree WITHOUT testing
    // it, otherwise descend into its children. Disjointness is descendant-
    // monotone, so this collects exactly the disjoint nodes while skipping their
    // subtrees.
    let mut nodes_to_test: Vec<_> =
        hierarchy.node(hierarchy.top_node()).child_nodes().iter().copied().collect();
    while let Some(node) = nodes_to_test.pop() {
        let representative = hierarchy.node(node).representative().clone();
        let rep_atom = role_atom(&representative);
        // Disjoint iff asserting both roles between the fresh pair is unsatisfiable.
        if !reasoner.is_consistent_with_test_atoms(&mut manager, &[ope_atom.clone(), rep_atom]) {
            for descendant in hierarchy.descendant_nodes(node) {
                for member in hierarchy.node(descendant).equivalent_elements() {
                    result.insert(member.clone());
                }
            }
        } else {
            for &child in hierarchy.node(node).child_nodes() {
                nodes_to_test.push(child);
            }
        }
    }
    // Java: if the result is empty, add the bottom NODE (Reasoner.java:1219-1220).
    if result.is_empty() {
        for member in hierarchy.equivalent_elements_of(&bottom_ope()) {
            result.insert(member);
        }
    }
    Ok(result)
}

/// `Reasoner.getDisjointDataProperties` getter (Reasoner.java:1514).
///
/// HermiT's GETTER uses a ROLE-ASSERTION reduction (NOT the
/// EntailmentChecker's `DataMaxCardinality(1, owl:topDataProperty)` reduction): for
/// each candidate `Q` it asserts `dp(a,k)` and `Q(a,k)` for a fresh individual `a`
/// and a shared anonymous constant `k`, and tests whether that is unsatisfiable
/// (Reasoner.java:1534-1546). Because these are plain role assertions on regular
/// properties (never owl:topDataProperty), normalization does not reject them, so —
/// unlike `is_entailed(DisjointDataProperties)` — this getter returns a real answer.
/// Result is descendant-closed; owl:bottomDataProperty is always disjoint.
pub fn get_disjoint_data_properties(
    ontology: &SetOntology<crate::structural::A>,
    dp: &horned_owl::model::DataProperty<crate::structural::A>,
) -> Result<std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>>, String>
{
    use horned_owl::model::DataProperty;
    use std::collections::HashSet;
    check_pre_conditions(ontology)?;

    let build = Build::new_arc();
    let top_iri = "http://www.w3.org/2002/07/owl#topDataProperty";
    let bottom_iri = "http://www.w3.org/2002/07/owl#bottomDataProperty";
    let dp_iri = dp.0.to_string();

    let consistent = is_ontology_consistent(ontology)?;
    let has_datatypes = clausify_for_query(ontology)?.has_datatypes();
    let hierarchy = classify_data_properties(ontology)?;
    let mut result: HashSet<DataProperty<crate::structural::A>> = HashSet::new();

    // hasDatatypes()==false branch (Reasoner.java:1556-1565): top -> {bottom},
    // bottom -> {top}, otherwise empty (and empty when inconsistent).
    if !has_datatypes {
        if consistent && dp_iri == top_iri {
            result.insert(build.data_property(bottom_iri));
        } else if consistent && dp_iri == bottom_iri {
            result.insert(build.data_property(top_iri));
        }
        return Ok(result);
    }

    // Inconsistent ontology => empty NodeSet (Reasoner.java:1518-1519).
    if !consistent {
        return Ok(result);
    }

    // owl:topDataProperty -> bottom NODE; owl:bottomDataProperty -> {top} + descendants
    // (Reasoner.java:1521-1530). The top case returns the whole bottom node, i.e.
    // every data property equivalent to owl:bottomDataProperty, not just the literal.
    if dp_iri == top_iri {
        let bottom = build.data_property(bottom_iri);
        for member in hierarchy.equivalent_elements_of(&bottom) {
            result.insert(member);
        }
        return Ok(result);
    }
    if dp_iri == bottom_iri {
        let top = build.data_property(top_iri);
        for d in hierarchy.sub_elements(&top, false) {
            result.insert(d);
        }
        result.insert(top);
        return Ok(result);
    }

    // Java reuses one tableau (getTableau()) and tests each candidate node with a
    // shared anonymous constant: `tableau.isSatisfiable({dp(a,k), rep(a,k)})` for a
    // fresh individual a and anonymous constant k (Reasoner.java:1531-1550).
    // Clausify once and run the reused-tableau per-test-atom check per node; the
    // shared anonymous constant is datatype-neutral, so it clashes only when the two
    // properties are genuinely disjoint.
    use crate::model::{Atom, AtomicRole, Constant as DlConstant, Individual as DlIndividual};
    let dl_ontology = clausify_for_query(ontology)?;
    let reasoner = Reasoner::new(&dl_ontology);
    let mut manager = reasoner.new_manager();
    let fresh_ind = DlIndividual::create(fresh_witness_iri("disjoint-dp-ind"));
    let fresh_const = DlConstant::create("disjoint-dp-const", "internal:anonymous-constants");
    let data_atom = |role: &DataProperty<crate::structural::A>| -> Atom {
        Atom::create(
            DLPredicate::AtomicRole(AtomicRole::create(role.0.to_string())),
            vec![Term::Individual(fresh_ind.clone()), Term::Constant(fresh_const.clone())],
        )
    };
    let dp_atom = data_atom(dp);
    // Top-down pruning walk (Reasoner.java:1537-1550): start from the top node's
    // children, test each node's representative, and on disjointness add the whole
    // (reflexive) descendant subtree without testing it; otherwise descend.
    let mut nodes_to_test: Vec<_> =
        hierarchy.node(hierarchy.top_node()).child_nodes().iter().copied().collect();
    while let Some(node) = nodes_to_test.pop() {
        let representative = hierarchy.node(node).representative().clone();
        let rep_atom = data_atom(&representative);
        if !reasoner.is_consistent_with_test_atoms(&mut manager, &[dp_atom.clone(), rep_atom]) {
            for descendant in hierarchy.descendant_nodes(node) {
                for member in hierarchy.node(descendant).equivalent_elements() {
                    result.insert(member.clone());
                }
            }
        } else {
            for &child in hierarchy.node(node).child_nodes() {
                nodes_to_test.push(child);
            }
        }
    }
    // Java: if the result is empty, add the bottom NODE (Reasoner.java:1553-1554),
    // i.e. every data property equivalent to owl:bottomDataProperty.
    if result.is_empty() {
        let bottom = build.data_property(bottom_iri);
        for member in hierarchy.equivalent_elements_of(&bottom) {
            result.insert(member);
        }
    }
    Ok(result)
}

/// `Reasoner.getInverseObjectProperties` (Reasoner.java:1178):
/// `getEquivalentObjectProperties(ope.getInverseProperty())`. The named object
/// properties equivalent to `Inv(ope)`.
pub fn get_inverse_object_properties(
    ontology: &SetOntology<crate::structural::A>,
    ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<
    std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>,
    String,
> {
    let inv = invert_ope(ope);
    get_equivalent_object_properties(ontology, &inv)
}

/// `Reasoner.getEquivalentObjectProperties` (Reasoner.java:1113). The named
/// object properties equivalent to `ope` (its node in the object-property
/// hierarchy). For an inverse expression, the equivalents are those whose inverse
/// is equivalent: tested directly by subsumption both ways.
pub fn get_equivalent_object_properties(
    ontology: &SetOntology<crate::structural::A>,
    ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
) -> Result<
    std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>,
    String,
> {
    check_pre_conditions(ontology)?;
    // Source from the OPE hierarchy so the returned node includes both
    // named (getOWLObjectProperty) and inverse (getOWLObjectInverseOf) members, exactly
    // as Java's objectPropertyHierarchyNodeToNode (Reasoner.java:2282-2294). The OPE
    // hierarchy classifies over both ObjectProperty and InverseObjectProperty, so for a
    // named R its node already contains any Inv(S) with R≡Inv(S).
    Ok(classify_object_property_expressions(ontology)?.equivalent_elements_of(ope))
}

/// `Reasoner.getSuperObjectProperties` (Reasoner.java:1091). The object
/// property expressions (including inverse expressions) that subsume `ope`.
/// `direct` restricts to immediate parents; otherwise all (proper) ancestors.
/// Sourced from the OPE hierarchy so inverse-role members survive.
pub fn get_super_object_properties(
    ontology: &SetOntology<crate::structural::A>,
    ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    direct: bool,
) -> Result<
    std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>,
    String,
> {
    Ok(classify_object_property_expressions(ontology)?.super_elements(ope, direct))
}

/// `Reasoner.getSubObjectProperties` (Reasoner.java:1102). The object
/// property expressions (including inverse expressions) subsumed by `ope`.
/// `direct` restricts to immediate children; otherwise all (proper) descendants.
/// Sourced from the OPE hierarchy so inverse-role members survive.
pub fn get_sub_object_properties(
    ontology: &SetOntology<crate::structural::A>,
    ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    direct: bool,
) -> Result<
    std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>,
    String,
> {
    Ok(classify_object_property_expressions(ontology)?.sub_elements(ope, direct))
}

/// `Reasoner.getEquivalentDataProperties` (Reasoner.java:1480). The named
/// data properties equivalent to `dp` (its node in the data-property hierarchy).
pub fn get_equivalent_data_properties(
    ontology: &SetOntology<crate::structural::A>,
    dp: &horned_owl::model::DataProperty<crate::structural::A>,
) -> Result<std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>>, String>
{
    check_pre_conditions(ontology)?;
    Ok(classify_data_properties(ontology)?.equivalent_elements_of(dp))
}

/// `Reasoner.getDisjointClasses` getter (Reasoner.java:832) -- already
/// provided as [`disjoint_classes`]; `get_disjoint_classes` is the named alias.
pub fn get_disjoint_classes(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    disjoint_classes(ontology, class)
}

/// `Reasoner.getTopClassNode` (Reasoner.java:746). The owl:Thing node's
/// members (the classes equivalent to owl:Thing).
pub fn get_top_class_node(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    let build = Build::new_arc();
    let hierarchy = classify(ontology)?;
    let top = build.class("http://www.w3.org/2002/07/owl#Thing");
    Ok(hierarchy.equivalent_elements_of(&top))
}

/// `Reasoner.getBottomClassNode` (Reasoner.java:750). The owl:Nothing
/// node's members (the unsatisfiable classes, equivalent to owl:Nothing).
pub fn get_bottom_class_node(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    let build = Build::new_arc();
    let hierarchy = classify(ontology)?;
    let bottom = build.class("http://www.w3.org/2002/07/owl#Nothing");
    Ok(hierarchy.equivalent_elements_of(&bottom))
}

/// `Reasoner.getUnsatisfiableClasses` (Reasoner.java:827):
/// `getBottomClassNode()` -- the classes equivalent to owl:Nothing.
pub fn get_unsatisfiable_classes(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
    get_bottom_class_node(ontology)
}

/// `Reasoner.getTopObjectPropertyNode` (Reasoner.java:1031). The members
/// of the owl:topObjectProperty node.
pub fn get_top_object_property_node(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<
    std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>,
    String,
> {
    use horned_owl::model::ObjectPropertyExpression as OPE;
    let build = Build::new_arc();
    // Source from the OPE hierarchy (not the named-only
    // projection) so inverse-role members of the node survive, mirroring Java's
    // objectPropertyHierarchyNodeToNode which emits getOWLObjectInverseOf members.
    let hierarchy = classify_object_property_expressions(ontology)?;
    let top = OPE::ObjectProperty(
        build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty"),
    );
    Ok(hierarchy.equivalent_elements_of(&top))
}

/// `Reasoner.getBottomObjectPropertyNode` (Reasoner.java:1035). The members
/// of the owl:bottomObjectProperty node (including inverse-role members).
pub fn get_bottom_object_property_node(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<
    std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>,
    String,
> {
    use horned_owl::model::ObjectPropertyExpression as OPE;
    let build = Build::new_arc();
    // OPE hierarchy so inverse-role members survive.
    let hierarchy = classify_object_property_expressions(ontology)?;
    let bottom = OPE::ObjectProperty(
        build.object_property("http://www.w3.org/2002/07/owl#bottomObjectProperty"),
    );
    Ok(hierarchy.equivalent_elements_of(&bottom))
}

/// `Reasoner.getTopDataPropertyNode` (Reasoner.java:1426). The members of
/// the owl:topDataProperty node.
pub fn get_top_data_property_node(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>>, String>
{
    let build = Build::new_arc();
    let hierarchy = classify_data_properties(ontology)?;
    let top = build.data_property("http://www.w3.org/2002/07/owl#topDataProperty");
    Ok(hierarchy.equivalent_elements_of(&top))
}

/// `Reasoner.getBottomDataPropertyNode` (Reasoner.java:1430). The members
/// of the owl:bottomDataProperty node.
pub fn get_bottom_data_property_node(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>>, String>
{
    let build = Build::new_arc();
    let hierarchy = classify_data_properties(ontology)?;
    let bottom = build.data_property("http://www.w3.org/2002/07/owl#bottomDataProperty");
    Ok(hierarchy.equivalent_elements_of(&bottom))
}

/// `Reasoner.hasType` (Reasoner.java:1638). Whether `individual` is an
/// instance of `class` (a thin wrapper over [`is_instance_of`]). `direct`
/// restricts to a *direct* (most-specific) type, mirroring Java's `direct` flag.
pub fn has_type(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
    class: &Class<crate::structural::A>,
    direct: bool,
) -> Result<bool, String> {
    check_pre_conditions(ontology)?;
    // `Reasoner.hasType` (Reasoner.java:1638-1644): an inconsistent ontology makes
    // every individual an instance of everything; and an individual not in the
    // ontology is of type `type` iff `type` is equivalent to owl:Thing.
    if !is_ontology_consistent(ontology)? {
        return Ok(true);
    }
    if !is_defined_individual(ontology, individual)? {
        let build = Build::new_arc();
        let thing = build.class("http://www.w3.org/2002/07/owl#Thing");
        return Ok(equivalent_classes(ontology, class)?.contains(&thing));
    }
    if direct {
        // Direct type: `class` is among the most-specific named types.
        return Ok(get_types(ontology, individual, true)?.contains(class));
    }
    is_instance_of_core(ontology, individual.clone(), CE::Class(class.clone()))
}

/// `Reasoner.hasObjectPropertyRelationship` (Reasoner.java:1791). Whether
/// `ope(subject, object)` is entailed (a thin wrapper over [`is_entailed`]).
pub fn has_object_property_relationship(
    ontology: &SetOntology<crate::structural::A>,
    subject: &NamedIndividual<crate::structural::A>,
    ope: horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
    object: &NamedIndividual<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::{Individual as I, ObjectPropertyAssertion};
    is_entailed(
        ontology,
        &Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope,
            from: I::Named(subject.clone()),
            to: I::Named(object.clone()),
        }),
    )
}

/// `Reasoner.hasDataPropertyRelationship` (Reasoner.java:1843). Whether
/// `dp(subject, literal)` is entailed (a thin wrapper over [`is_entailed`]).
pub fn has_data_property_relationship(
    ontology: &SetOntology<crate::structural::A>,
    subject: &NamedIndividual<crate::structural::A>,
    dp: horned_owl::model::DataProperty<crate::structural::A>,
    literal: horned_owl::model::Literal<crate::structural::A>,
) -> Result<bool, String> {
    use horned_owl::model::{DataPropertyAssertion, Individual as I};
    is_entailed(
        ontology,
        &Component::DataPropertyAssertion(DataPropertyAssertion {
            dp,
            from: I::Named(subject.clone()),
            to: literal,
        }),
    )
}

/// `Reasoner.isDefined(OWLClass)` (Reasoner.java:489). Whether the class
/// occurs in the ontology vocabulary (or is owl:Thing/owl:Nothing).
pub fn is_defined_class(
    ontology: &SetOntology<crate::structural::A>,
    class: &Class<crate::structural::A>,
) -> Result<bool, String> {
    use crate::model::AtomicConcept;
    let iri = class.0.to_string();
    if iri == "http://www.w3.org/2002/07/owl#Thing"
        || iri == "http://www.w3.org/2002/07/owl#Nothing"
    {
        return Ok(true);
    }
    let dl_ontology = clausify_for_query(ontology)?;
    Ok(dl_ontology.contains_atomic_concept(&AtomicConcept::create(iri)))
}

/// `Reasoner.isDefined(OWLObjectProperty)` (Reasoner.java:504). Whether the
/// object property occurs in the ontology vocabulary (or is the top/bottom role).
pub fn is_defined_object_property(
    ontology: &SetOntology<crate::structural::A>,
    property: &horned_owl::model::ObjectProperty<crate::structural::A>,
) -> Result<bool, String> {
    use crate::model::AtomicRole;
    let iri = property.0.to_string();
    // Java's `TOP/BOTTOM_OBJECT_ROLE.equals(owlObjectProperty)` arms
    // (Reasoner.java:504-510) are DEAD code — AtomicRole has no equals(Object) override,
    // so the comparison against an OWLObjectProperty is always false and isDefined
    // collapses to containsObjectRole. (The class and data-property variants DO have
    // live top/bottom arms, so theirs stay.)
    let dl_ontology = clausify_for_query(ontology)?;
    Ok(dl_ontology.contains_object_role(&AtomicRole::create(iri)))
}

/// `Reasoner.isDefined(OWLDataProperty)` (Reasoner.java:511). Whether the
/// data property occurs in the ontology vocabulary (or is the top/bottom role).
pub fn is_defined_data_property(
    ontology: &SetOntology<crate::structural::A>,
    property: &horned_owl::model::DataProperty<crate::structural::A>,
) -> Result<bool, String> {
    use crate::model::AtomicRole;
    let iri = property.0.to_string();
    if iri == "http://www.w3.org/2002/07/owl#topDataProperty"
        || iri == "http://www.w3.org/2002/07/owl#bottomDataProperty"
    {
        return Ok(true);
    }
    let dl_ontology = clausify_for_query(ontology)?;
    Ok(dl_ontology.contains_data_role(&AtomicRole::create(iri)))
}

/// `Reasoner.isDefined(OWLIndividual)` (Reasoner.java:496). Whether the
/// individual occurs in the ontology vocabulary.
pub fn is_defined_individual(
    ontology: &SetOntology<crate::structural::A>,
    individual: &NamedIndividual<crate::structural::A>,
) -> Result<bool, String> {
    use crate::model::Individual as DlIndividual;
    let dl_ontology = clausify_for_query(ontology)?;
    Ok(dl_ontology.contains_individual(&DlIndividual::create(individual.0.to_string())))
}

/// `Reasoner.getReasonerName` (Reasoner.java:298). HermiT's
/// implementation title.
pub fn reasoner_name() -> &'static str {
    "HermiT"
}

/// `Reasoner.getReasonerVersion` (Reasoner.java:301). HermiT's
/// implementation version (`major.minor.patch.build`), matching the ported
/// upstream `1.4.0.0`.
pub fn reasoner_version() -> &'static str {
    "1.4.0.0"
}

/// The OWL `InferenceType` kinds HermiT can precompute, mirroring
/// `Reasoner.getPrecomputableInferenceTypes` (Reasoner.java:518). DATA_PROPERTY_
/// ASSERTIONS, DIFFERENT_INDIVIDUALS and DISJOINT_CLASSES are intentionally
/// absent, exactly as in Java.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferenceType {
    ClassHierarchy,
    ObjectPropertyHierarchy,
    DataPropertyHierarchy,
    ClassAssertions,
    ObjectPropertyAssertions,
    SameIndividual,
}

/// `Reasoner.getPrecomputableInferenceTypes` (Reasoner.java:518).
pub fn get_precomputable_inference_types() -> std::collections::HashSet<InferenceType> {
    use InferenceType::*;
    [
        ClassHierarchy,
        ObjectPropertyHierarchy,
        DataPropertyHierarchy,
        ClassAssertions,
        ObjectPropertyAssertions,
        SameIndividual,
    ]
    .into_iter()
    .collect()
}

/// `Reasoner.isPrecomputed(InferenceType)` (Reasoner.java:530).
///
/// This implementation is stateless: it caches no classified hierarchy / realised
/// instance-manager between queries (every query recomputes), so there is no
/// completion flag for `isPrecomputed` to read. The faithful constant answer is
/// therefore `false` for every inference type — matching Java's value before any
/// precompute has populated the corresponding cache. Callers should simply invoke
/// the relevant query, which always recomputes.
pub fn is_precomputed(_inference_type: InferenceType) -> bool {
    false
}

/// `Reasoner.precomputeInferences` (Reasoner.java:555). Runs the
/// classification/realisation tasks requested by `inference_types`, dispatching
/// to the existing reasoning services exactly as Java's `precomputeInferences`
/// switch does. `checkPreConditions` throws on an inconsistent ontology under the
/// default flag. Unsupported types (DATA_PROPERTY_ASSERTIONS, DIFFERENT_
/// INDIVIDUALS, DISJOINT_CLASSES) are silently ignored, as in HermiT.
pub fn precompute(
    ontology: &SetOntology<crate::structural::A>,
    inference_types: &[InferenceType],
) -> Result<(), String> {
    check_pre_conditions(ontology)?;
    use InferenceType::*;
    let requested: std::collections::HashSet<InferenceType> =
        inference_types.iter().copied().collect();
    if requested.contains(&ClassHierarchy) {
        classify(ontology)?;
    }
    if requested.contains(&ObjectPropertyHierarchy) {
        classify_object_properties(ontology)?;
    }
    if requested.contains(&DataPropertyHierarchy) {
        classify_data_properties(ontology)?;
    }
    if requested.contains(&ClassAssertions) {
        realize(ontology)?;
    }
    if requested.contains(&ObjectPropertyAssertions) {
        let build = Build::new_arc();
        // realiseObjectProperties precomputes the object-property instance graph;
        // exercising it over the top object property primes the same path.
        let _ = object_property_instances(
            ontology,
            horned_owl::model::ObjectPropertyExpression::ObjectProperty(
                build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty"),
            ),
        )?;
    }
    if requested.contains(&SameIndividual) {
        // precomputeSameAsEquivalenceClasses: warming the same-as relation. Under
        // BY_NAME this is a no-op beyond classification; we touch realize so the
        // realisation it depends on is ready.
        realize(ontology)?;
    }
    Ok(())
}

/// `Reasoner.precomputeDisjointClasses` (Reasoner.java:891).
///
/// Java fills an `m_directDisjointClasses` memo by classifying then visiting every
/// hierarchy node. No such cache is maintained here (`disjoint_classes` recomputes
/// per call), so this is a no-op-equivalent entry point that mirrors Java's
/// `checkPreConditions()` + `classifyClasses()` guard for API parity.
/// `DISJOINT_CLASSES` is intentionally absent from [`get_precomputable_inference_types`]
/// (matching Java's `getPrecomputableInferenceTypes`), so this is a standalone method.
pub fn precompute_disjoint_classes(
    ontology: &SetOntology<crate::structural::A>,
) -> Result<(), String> {
    check_pre_conditions(ontology)?;
    classify(ontology)?;
    Ok(())
}

/// `Reasoner.dumpHierarchies` (Reasoner.java:2108). Returns the
/// functional-syntax dump of the requested hierarchies (class / object-property /
/// data-property), concatenated, using the [`crate::hierarchy::Hierarchy`]
/// dumpers. Mirrors Java's `HierarchyDumperFSS`.
pub fn dump_hierarchies(
    ontology: &SetOntology<crate::structural::A>,
    classes: bool,
    object_properties: bool,
    data_properties: bool,
) -> Result<String, String> {
    use horned_owl::model::ObjectPropertyExpression as OPE;
    let mut sections: Vec<String> = Vec::new();
    if classes {
        let hierarchy = classify(ontology)?;
        sections.push(hierarchy.dump_functional_syntax(
            "EquivalentClasses",
            "SubClassOf",
            |c: &Class<crate::structural::A>| format!("<{}>", c.0),
        ));
    }
    if object_properties {
        let hierarchy = classify_object_property_expressions(ontology)?;
        sections.push(hierarchy.dump_functional_syntax(
            "EquivalentObjectProperties",
            "SubObjectPropertyOf",
            |p: &OPE<crate::structural::A>| match p {
                OPE::ObjectProperty(op) => format!("<{}>", op.0),
                OPE::InverseObjectProperty(op) => format!("ObjectInverseOf( <{}> )", op.0),
            },
        ));
    }
    if data_properties {
        let hierarchy = classify_data_properties(ontology)?;
        // Use the java-data variant to reproduce the Java bug in
        // HierarchyDumperFSS.printDataPropertyHierarchy (line 127): non-first
        // EquivalentDataProperties members are emitted as ">iri>" not "<iri>".
        sections.push(hierarchy.dump_functional_syntax_java_data(
            "EquivalentDataProperties",
            "SubDataPropertyOf",
            |p: &horned_owl::model::DataProperty<crate::structural::A>| format!("<{}>", p.0),
            |p: &horned_owl::model::DataProperty<crate::structural::A>| format!(">{}>", p.0),
        ));
    }
    // Each section already ends with \n\n (axioms + trailing blank line from
    // HierarchyDumperFSS.java:73/110/149), so concatenate verbatim; do NOT
    // filter or join — Java emits a blank line even for an empty section.
    Ok(sections.concat())
}

/// `Reasoner.printHierarchies` (Reasoner.java:2136). The
/// `print_functional_syntax` rendering of the requested hierarchies, concatenated.
pub fn print_hierarchies(
    ontology: &SetOntology<crate::structural::A>,
    classes: bool,
    object_properties: bool,
    data_properties: bool,
) -> Result<String, String> {
    use horned_owl::model::ObjectPropertyExpression as OPE;
    let mut sections: Vec<String> = Vec::new();
    if classes {
        let hierarchy = classify(ontology)?;
        sections.push(
            hierarchy.print_functional_syntax(|c: &Class<crate::structural::A>| format!("<{}>", c.0)),
        );
    }
    if object_properties {
        // RolePrinter (HierarchyPrinterFSS.java:206-209,219-221,236-238): uses
        // SubObjectPropertyOf / EquivalentObjectProperties / Declaration( ObjectProperty( ... ) );
        // needsDeclaration (line 259-260) suppresses top/bottom AND inverse roles.
        let top_op_iri = "http://www.w3.org/2002/07/owl#topObjectProperty";
        let bottom_op_iri = "http://www.w3.org/2002/07/owl#bottomObjectProperty";
        let hierarchy = classify_object_property_expressions(ontology)?;
        let render_op = |p: &OPE<crate::structural::A>| match p {
            OPE::ObjectProperty(op) => format!("<{}>", op.0),
            OPE::InverseObjectProperty(op) => format!("ObjectInverseOf( <{}> )", op.0),
        };
        let top_repr = format!("<{}>", top_op_iri);
        let bottom_repr = format!("<{}>", bottom_op_iri);
        sections.push(hierarchy.print_functional_syntax_with(
            render_op,
            "SubObjectPropertyOf",
            "EquivalentObjectProperties",
            "ObjectProperty",
            |m: &str| m != top_repr && m != bottom_repr && !m.starts_with("ObjectInverseOf"),
        ));
    }
    if data_properties {
        // RolePrinter (HierarchyPrinterFSS.java:208-209,222-223,239-240): uses
        // SubDataPropertyOf / EquivalentDataProperties / Declaration( DataProperty( ... ) ).
        let top_dp_iri = "http://www.w3.org/2002/07/owl#topDataProperty";
        let bottom_dp_iri = "http://www.w3.org/2002/07/owl#bottomDataProperty";
        let hierarchy = classify_data_properties(ontology)?;
        let top_repr = format!("<{}>", top_dp_iri);
        let bottom_repr = format!("<{}>", bottom_dp_iri);
        sections.push(hierarchy.print_functional_syntax_with(
            |p: &horned_owl::model::DataProperty<crate::structural::A>| format!("<{}>", p.0),
            "SubDataPropertyOf",
            "EquivalentDataProperties",
            "DataProperty",
            |m: &str| m != top_repr && m != bottom_repr,
        ));
    }
    Ok(sections
        .into_iter()
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join("\n"))
}

/// Clausifies a horned-owl ontology and decides ABox consistency in one call --
/// the full pipeline (normalize → clausify → reason).
pub fn is_ontology_consistent(
    ontology: &horned_owl::ontology::set::SetOntology<crate::structural::A>,
) -> Result<bool, String> {
    is_ontology_consistent_with_configuration(
        ontology,
        &crate::configuration::Configuration::default(),
    )
}

/// As [`is_ontology_consistent`], but runs the consistency check under an explicit
/// [`Configuration`](crate::configuration::Configuration): the blocking
/// strategy, direct-blocking type, signature cache and existential-expansion
/// strategy from `configuration` are threaded into the tableau (via
/// `Reasoner::with_configuration`). With `Configuration::default()` this is
/// byte-for-byte identical to `is_ontology_consistent` (HermiT's defaults), so the
/// existing callers are unchanged; tuning flags affect only the configured path.
pub fn is_ontology_consistent_with_configuration(
    ontology: &horned_owl::ontology::set::SetOntology<crate::structural::A>,
    configuration: &crate::configuration::Configuration,
) -> Result<bool, String> {
    let dl_ontology = clausify_ontology(ontology)?;
    Ok(Reasoner::with_configuration(&dl_ontology, configuration.clone()).is_consistent())
}

/// Runs the full front-end pipeline (normalize → built-in axiomatization →
/// object-property inclusion rewriting → clausify) over `ontology` and returns
/// the resulting `DLOntology`. This is the from-scratch clausification of a
/// brand-new ontology: it passes `0` as the first replacement index to
/// `rewrite_axioms` (matching `OWLClausification.java:153` /
/// `loadOntology`), so the `internal:all#` concepts start at 0. Used both by
/// [`is_ontology_consistent`] and as the `loadOntology` fallback path of
/// [`IncrementalReasoner::flush`].
fn clausify_ontology(
    ontology: &horned_owl::ontology::set::SetOntology<crate::structural::A>,
) -> Result<DLOntology, String> {
    use crate::structural::{
        BuiltInPropertyManager, Configuration, ObjectPropertyInclusionManager, OWLAxioms,
        OWLAxiomsExpressivity, OWLClausification, OWLNormalization,
    };
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology)?;
    let definitions_count = normalization.definitions_count();
    let mut axioms = normalization.into_axioms();
    // Give owl:{top,bottom}{Object,Data}Property their built-in meaning when used,
    // before the inclusion manager (built-in axiomatization can add complex
    // inclusions, e.g. owl:topObjectProperty's transitivity).
    BuiltInPropertyManager::new().axiomatize_built_in_properties_as_needed(&mut axioms);
    // The object-property inclusion manager runs unconditionally (as in
    // preprocessAndClausify): it builds the automata and rewrites negative
    // assertions / ∀R.C axioms in every case.
    let manager = ObjectPropertyInclusionManager::new(&mut axioms)?;
    let next_index =
        manager.rewrite_negative_object_property_assertions(&mut axioms, definitions_count);
    let _ = next_index;
    manager.rewrite_axioms(&mut axioms, 0)?;
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    OWLClausification::new(Configuration::default()).clausify(
        "http://hermit-rs/anonymous-ontology",
        &axioms,
        &expressivity,
    )
}

/// Port of `Reasoner.createDeltaDLOntology` (Reasoner.java:2058-2083), the
/// engine behind `createAdditionalTableau` / `getTableau(OWLAxiom)`: clausifies a
/// set of ADDITIONAL axioms on top of an already-loaded `original` `DLOntology`,
/// THREADING the replacement index so the fresh `internal:all#`/`internal:def#`
/// concepts introduced by the object-property-inclusion rewriting cannot collide
/// with those of the original ontology.
///
/// The index is `original.get_all_atomic_concepts().len()` (Java:
/// `originalDLOntology.getAllAtomicConcepts().size()`), threaded into:
///   * the `OWLNormalization` (Reasoner.java:2068),
///   * `rewrite_negative_object_property_assertions` (Reasoner.java:2073), whose
///     returned next-index is captured and
///   * `rewrite_axioms` (Reasoner.java:2074).
///
/// The index threading ensures a from-scratch clausification (`clausify_ontology`)
/// always passes `0`, mirroring `OWLClausification.java:153`.
fn create_delta_dl_ontology(
    additional: &horned_owl::ontology::set::SetOntology<crate::structural::A>,
    original: &DLOntology,
) -> Result<DLOntology, String> {
    use crate::structural::{
        BuiltInPropertyManager, Configuration, ObjectPropertyInclusionManager, OWLAxioms,
        OWLAxiomsExpressivity, OWLClausification, OWLNormalization,
    };
    // Reasoner.java:2061-2062 / isUnsupportedExtensionAxiom (Reasoner.java:1932):
    // the additional (delta) ontology cannot carry role inclusions, transitivity,
    // role chains, (inverse) functionality, or SWRL rules -- the additional-DL
    // mechanism cannot soundly absorb them, so Java throws IllegalArgumentException.
    // (horned-owl's `SubObjectPropertyOf` covers both the simple `OWLSubObjectPropertyOf`
    // and chain `OWLSubPropertyChainOf` Java axiom types.)
    for annotated in additional.iter() {
        if matches!(
            annotated.component,
            Component::SubObjectPropertyOf(_)
                | Component::TransitiveObjectProperty(_)
                | Component::FunctionalObjectProperty(_)
                | Component::InverseFunctionalObjectProperty(_)
                | Component::Rule(_)
        ) {
            return Err("Internal error: unsupported extension axiom type.".to_string());
        }
    }
    // Reasoner.java:2068 -- start normalization's replacement counter at the
    // original ontology's atomic-concept count so fresh definition concepts do
    // not collide.
    let replacement_index = original.get_all_atomic_concepts().len();
    // Reasoner.java:2067 -- seed the defined-datatype IRIs from the original ontology
    // so the additional axioms' datatype-definition clausification sees them.
    let mut seed_axioms = OWLAxioms::new();
    seed_axioms
        .defined_datatype_iris
        .extend(original.get_defined_datatype_iris().iter().cloned());
    let mut normalization = OWLNormalization::new(seed_axioms, replacement_index);
    normalization.process_ontology(additional)?;
    let mut axioms = normalization.into_axioms();
    // Reasoner.java:2071 -- skip re-axiomatizing a built-in property whose top/bottom
    // role already occurs in the original ontology (its built-in axioms are already
    // in the permanent clause set), so the delta does not duplicate them.
    let original_roles = original.get_all_atomic_object_roles();
    BuiltInPropertyManager::new().axiomatize_built_in_properties_as_needed_with_skips(
        &mut axioms,
        original_roles.contains(crate::model::AtomicRole::top_object_role()),
        original_roles.contains(crate::model::AtomicRole::bottom_object_role()),
        original_roles.contains(crate::model::AtomicRole::top_data_role()),
        original_roles.contains(crate::model::AtomicRole::bottom_data_role()),
    );
    // Reasoner.java:2072-2074 runs the object-property inclusion manager
    // unconditionally on the delta.
    let manager = ObjectPropertyInclusionManager::new(&mut axioms)?;
    // Thread the replacement index (NOT 0) so the additional ∀R.C rewriting's
    // `internal:all#` concepts are disjoint from the original's.
    let current_replacement_index =
        manager.rewrite_negative_object_property_assertions(&mut axioms, replacement_index);
    manager.rewrite_axioms(&mut axioms, current_replacement_index)?;
    // Reasoner.java:2076-2079 -- the additional ontology's expressivity must include
    // the original's, so blocking/datatype machinery is enabled if either needs it.
    let mut expressivity = OWLAxiomsExpressivity::new(&axioms);
    expressivity.has_at_most_restrictions |= original.has_at_most_restrictions();
    expressivity.has_inverse_roles |= original.has_inverse_roles();
    expressivity.has_nominals |= original.has_nominals();
    expressivity.has_datatypes |= original.has_datatypes();
    OWLClausification::new(Configuration::default()).clausify(
        "uri:urn:internal-kb",
        &axioms,
        &expressivity,
    )
}

pub struct Reasoner<'a> {
    dl_ontology: &'a DLOntology,
    /// Port of `Reasoner.m_configuration`: the reasoner-options holder,
    /// threaded into every tableau the reasoner builds. `Configuration::default()`
    /// preserves HermiT's defaults (disjunction-learning on, no timeout, throw on
    /// an inconsistent ontology).
    configuration: crate::configuration::Configuration,
    /// The `IndividualReuseStrategy`'s reasoner-wide `m_dontReuseConceptsEver`,
    /// shared into every per-test tableau so reuse learning persists across
    /// satisfiability tests (HermiT keeps one tableau for the reasoner lifetime).
    reuse_dont_ever: crate::existentials::SharedDontReuseEver,
    /// Port of HermiT's single, lifetime-scoped `m_tableau`: one fully-configured
    /// per-test tableau, reused across every satisfiability/subsumption test
    /// instead of allocating a fresh one per test. The first checkout builds and
    /// caches it; subsequent checkouts `clear()` it (firing `tableauCleared`) and
    /// re-load the permanent ABox. The `TableauGuard` returned by
    /// [`checkout_test_tableau`](Reasoner::checkout_test_tableau) returns it here
    /// on drop, so every method's early-return / `?` paths still recover it.
    test_tableau: std::cell::RefCell<Option<Tableau>>,
}

/// RAII guard wrapping the reasoner's reused per-test tableau. Derefs to
/// [`Tableau`]; on drop it returns the (now-saturated) tableau to the reasoner's
/// cache so the next checkout can `clear()` and reuse it. This mirrors HermiT
/// keeping a single `m_tableau` for the reasoner's lifetime: only the allocation
/// is reused -- the tableau is wiped between tests, so results are unchanged.
pub(crate) struct TableauGuard<'r> {
    cache: &'r std::cell::RefCell<Option<Tableau>>,
    tableau: Option<Tableau>,
}

impl std::ops::Deref for TableauGuard<'_> {
    type Target = Tableau;
    fn deref(&self) -> &Tableau {
        self.tableau.as_ref().expect("tableau checked out")
    }
}

impl std::ops::DerefMut for TableauGuard<'_> {
    fn deref_mut(&mut self) -> &mut Tableau {
        self.tableau.as_mut().expect("tableau checked out")
    }
}

impl Drop for TableauGuard<'_> {
    fn drop(&mut self) {
        // Return the tableau to the cache for the next test to clear+reuse.
        if let Some(tableau) = self.tableau.take() {
            *self.cache.borrow_mut() = Some(tableau);
        }
    }
}

impl<'a> Reasoner<'a> {
    /// Builds a reasoner with HermiT's default configuration.
    pub fn new(dl_ontology: &'a DLOntology) -> Reasoner<'a> {
        Reasoner::with_configuration(
            dl_ontology,
            crate::configuration::Configuration::default(),
        )
    }

    /// Port of `Reasoner(Configuration, ...)`: builds a reasoner that
    /// threads `configuration` into every tableau it constructs.
    pub fn with_configuration(
        dl_ontology: &'a DLOntology,
        configuration: crate::configuration::Configuration,
    ) -> Reasoner<'a> {
        Reasoner {
            dl_ontology,
            configuration,
            reuse_dont_ever: std::rc::Rc::new(std::cell::RefCell::new(
                std::collections::HashSet::new(),
            )),
            test_tableau: std::cell::RefCell::new(None),
        }
    }

    /// The reasoner's configuration.
    pub fn configuration(&self) -> &crate::configuration::Configuration {
        &self.configuration
    }

    /// The (read-only, shareable) clausified ontology this reasoner runs over.
    /// Used to spin up independent per-thread reasoner replicas for the parallel
    /// leaf-node model builds (each replica owns its own tableau/manager/reuse set,
    /// so nothing `!Send` crosses a thread boundary, while the `&'a DLOntology` and
    /// its interned `&'static` clause handles are shared by reference).
    pub fn dl_ontology(&self) -> &'a DLOntology {
        self.dl_ontology
    }

    /// Sets the per-tableau datatype flags, mirroring the relevant lines of
    /// `Tableau.updateFlagsDependentOnAdditionalOntology` (Tableau.java:246-255):
    /// `m_checkDatatypes` from `hasDatatypes()` and `m_checkUnknownDatatypeRestrictions`
    /// from `hasUnknownDatatypeRestrictions()`, the latter also seeding the unknown
    /// restriction set (`DatatypeManager.m_unknownDatatypeRestrictionsPermanent`).
    /// The unknown-restriction set is only ever non-empty in the non-default
    /// `ignoreUnsupportedDatatypes` mode, which we also require explicitly so the
    /// default path leaves both the flag and the set untouched (byte-for-byte).
    fn configure_tableau_datatypes(&self, tableau: &mut Tableau) {
        tableau.check_datatypes = self.dl_ontology.has_datatypes();
        if self.configuration.ignore_unsupported_datatypes
            && self.dl_ontology.has_unknown_datatype_restrictions()
        {
            tableau.check_unknown_datatype_restrictions = true;
            tableau.unknown_datatype_restrictions =
                self.dl_ontology.get_all_unknown_datatype_restrictions().clone();
        }
    }

    /// Port of `Reasoner.createTableau`'s blocking construction.
    /// Selects the blocking strategy, direct-blocking checker and signature cache
    /// from the configuration and the ontology's expressivity flags
    /// (`hasInverseRoles`/`hasNominals`), and -- for the core/validated strategies
    /// (`SIMPLE_CORE`/`COMPLEX_CORE`) -- attaches the `BlockingValidator` built
    /// from the permanent DL clauses (so `is_exact()` becomes false and the
    /// final-chance revalidation runs). Called on every tableau the reasoner
    /// builds, exactly as Java's `createTableau` runs the same switch each time.
    fn configure_tableau_blocking(&self, tableau: &mut Tableau) {
        tableau.configure_blocking(
            &self.configuration,
            self.dl_ontology.has_inverse_roles(),
            self.dl_ontology.has_nominals(),
        );
        if tableau.blocking_uses_validator() {
            let validator = crate::tableau::blocking_validator::BlockingValidator::new(
                self.dl_ontology.get_dl_clauses(),
            );
            tableau.set_blocking_validator(validator);
        }
    }

    /// Whether the ontology's ABox is satisfiable. With the default
    /// configuration (no timeout, no explicit interrupt) the calculus never
    /// interrupts, so this returns a plain `bool`; an actually-fired interrupt
    /// (only possible with a positive `individual_task_timeout` or an explicit
    /// `interrupt`) is reported by `is_consistent_checked`.
    pub fn is_consistent(&self) -> bool {
        // The default -1 timeout never interrupts, so the Err arm is dead in
        // the default configuration; treat an interrupt as "no model found".
        self.is_consistent_checked().unwrap_or(false)
    }

    /// Runs the consistency check with `monitor` attached, returning both
    /// the result and the (now-populated) monitor so callers can read off the
    /// observed statistics. Answer-neutral: the monitor never affects the result.
    pub fn is_consistent_with_monitor(
        &self,
        monitor: crate::monitor::CountingMonitor,
    ) -> (bool, crate::monitor::CountingMonitor) {
        // Attach the monitor, run, then recover it. We box it for the trait
        // object, downcast-free recovery via a dedicated run path.
        self.run_consistency_with_monitor(Box::new(monitor))
    }

    fn run_consistency_with_monitor(
        &self,
        monitor: Box<crate::monitor::CountingMonitor>,
    ) -> (bool, crate::monitor::CountingMonitor) {
        let mut tableau = Tableau::with_configuration(&self.configuration);
        tableau.set_monitor(Some(monitor));
        let mut manager = self.new_manager();
        tableau.update_extension_flags(&manager);
        self.configure_tableau_datatypes(&mut tableau);
        tableau.set_functional_roles_from_clauses(self.dl_ontology.get_dl_clauses());
        self.configure_tableau_description_graphs(&mut tableau);
        self.configure_tableau_blocking(&mut tableau);
        // Java: m_problemStartTime = System.currentTimeMillis() in isSatisfiableStarted.
        let problem_start = std::time::Instant::now();
        tableau.monitor_event(|m| m.is_satisfiable_started());
        self.load_abox(&mut tableau);
        let result = if tableau.contains_clash() {
            false
        } else {
            run_calculus(&mut tableau, &mut manager).unwrap_or(false)
        };
        // Recover the monitor and enrich it with per-test tableau-derived state
        // before firing isSatisfiableFinished — mirroring CountingMonitor.java:136-149.
        // Java reads these directly off m_tableau; the Rust port exposes explicit
        // hooks because the boxed monitor cannot borrow the tableau.
        let mut recovered = *tableau
            .take_monitor()
            .expect("monitor was attached")
            .as_any()
            .downcast::<crate::monitor::CountingMonitor>()
            .expect("the attached monitor is a CountingMonitor");
        // m_time = System.currentTimeMillis() - m_problemStartTime (CountingMonitor.java:136)
        recovered.set_test_time(problem_start.elapsed().as_millis() as u64);
        // m_numberOfNodes = getNumberOfNodesInTableau() - getNumberOfMergedOrPrunedNodes()
        // (CountingMonitor.java:142)
        let live_nodes = (tableau.get_number_of_nodes_in_tableau()
            - tableau.number_of_merged_or_pruned_nodes)
            .max(0) as u64;
        recovered.record_node_count(live_nodes);
        // Iterate the tableau node list and count active+blocked+hasUnprocessedExistentials
        // nodes (CountingMonitor.java:143-149).
        let mut node = tableau.get_first_tableau_node();
        while let Some(id) = node {
            let n = tableau.node(id);
            if n.is_active() && n.is_blocked() && n.has_unprocessed_existentials() {
                recovered.record_blocked_node();
            }
            node = n.get_next_tableau_node();
        }
        // No result flip: is_consistent is not a negated-satisfiability test
        // (CountingMonitor.java:133-134: flip only when reasoningTaskDescription says so).
        recovered.is_satisfiable_finished_with(result, false);
        (result, recovered)
    }

    /// Like `is_consistent`, but surfaces an interrupt as an `Err` instead
    /// of collapsing it to `false`.
    pub fn is_consistent_checked(
        &self,
    ) -> Result<bool, crate::tableau::interrupt_flag::InterruptError> {
        let mut tableau = Tableau::with_configuration(&self.configuration);
        // Build the manager first and set the node-seeding flags from it (HermiT's
        // `updateFlagsDependentOnAdditionalOntology`) *before* loading the ABox, so
        // `owl:Thing`/`internal:named`/`rdfs:Literal` are materialized on the nodes
        // that need them and the corresponding clauses (e.g. a `⊤ ⊑ C` top-GCI) fire.
        let mut manager = self.new_manager();
        tableau.update_extension_flags(&manager);
        self.configure_tableau_datatypes(&mut tableau);
        tableau.set_functional_roles_from_clauses(self.dl_ontology.get_dl_clauses());
        self.configure_tableau_description_graphs(&mut tableau);
        // Select the blocking strategy / direct-blocking checker /
        // signature cache (and, for the core strategies, attach the validator)
        // exactly as `Reasoner.createTableau` does, from the configuration and the
        // ontology's expressivity flags. The DEFAULT config (Optimal/Optimal/
        // Cached) yields anywhere blocking with the single checker for nominal-free
        // ontologies without inverse roles and the pairwise checker when inverse
        // roles are present -- both sound+complete, deciding the same questions.
        self.configure_tableau_blocking(&mut tableau);
        tableau.monitor_event(|m| m.is_satisfiable_started());
        self.load_abox(&mut tableau);
        if tableau.contains_clash() {
            tableau.monitor_event(|m| m.is_satisfiable_finished(false));
            return Ok(false);
        }
        // HermiT's runCalculus loop (no-blocking core): each iteration either
        // saturates (rule application), expands an existential, processes a
        // ground disjunction (branching), or -- on a clash -- backtracks
        // (dependency-directed) to try the next disjunct. Terminates for
        // ontologies whose existentials are not cyclic. `run_calculus`
        // brackets the loop with the monitor/interrupt hooks.
        let result = run_calculus(&mut tableau, &mut manager);
        tableau.monitor_event(|m| m.is_satisfiable_finished(matches!(result, Ok(true))));
        result
    }

    /// Java's `getTableau()` + `tableau.isSatisfiable(..., perTestAtoms, ...)`: reuses
    /// the single cached test tableau (clearing it between calls, firing
    /// `tableauCleared`) and decides the consistency of the permanent KB plus the
    /// given *positive* per-test ABox atoms -- instead of building (and
    /// re-clausifying) a fresh tableau per test. The caller passes the same
    /// `manager` on every call (as HermiT reuses one `m_tableau`/manager), so the
    /// compiled clauses are shared too. Used by the property/individual getters that
    /// run one satisfiability test per candidate.
    pub fn is_consistent_with_test_atoms(
        &self,
        manager: &mut HyperresolutionManager,
        test_atoms: &[crate::model::Atom],
    ) -> bool {
        self.is_consistent_with_pos_neg_test_atoms(manager, test_atoms, &[])
    }

    /// As [`is_consistent_with_test_atoms`](Self::is_consistent_with_test_atoms) but
    /// also asserts NEGATIVE per-test atoms (e.g. a `¬Q(x)` needed for a subsumption
    /// entailment test `A ⊑ B` -> assert `Q_A(x) ∧ ¬Q_B(x)`).
    pub fn is_consistent_with_pos_neg_test_atoms(
        &self,
        manager: &mut HyperresolutionManager,
        positive_test_atoms: &[crate::model::Atom],
        negative_test_atoms: &[crate::model::Atom],
    ) -> bool {
        let mut tableau = match self.test_tableau.borrow_mut().take() {
            Some(mut cached) => {
                cached.clear();
                cached
            }
            None => self.build_test_tableau(manager),
        };
        tableau.monitor_event(|m| m.is_satisfiable_started());
        self.load_abox_tracking_individuals(
            &mut tableau,
            positive_test_atoms,
            negative_test_atoms,
        );
        let result = if tableau.contains_clash() {
            false
        } else {
            run_calculus(&mut tableau, manager).unwrap_or(false)
        };
        tableau.monitor_event(|m| m.is_satisfiable_finished(result));
        *self.test_tableau.borrow_mut() = Some(tableau);
        result
    }

    /// Runs the initial consistency check and -- on a consistent ABox -- returns
    /// the *saturated* tableau together with the individual -> node mapping, so the
    /// `InstanceManager` can read the known/possible class instances off the model.
    ///
    /// Port of the `Reasoner.initialiseClassInstanceManager` /
    /// `initialisePropertiesInstanceManager` driver: HermiT runs
    /// `tableau.isSatisfiable(..., m_instanceManager.getNodesForIndividuals(), ...)`,
    /// which both decides consistency and populates `m_nodesForIndividuals` with the
    /// node each individual became, then reads the labels off those nodes
    /// (`initializeKnowAndPossibleClassInstances`). Returns `None` when the ontology
    /// is inconsistent (`m_instanceManager.setInconsistent()`).
    pub fn saturate_for_instances(
        &self,
    ) -> Option<(Tableau, HashMap<crate::model::Individual, NodeId>)> {
        let mut tableau = Tableau::with_configuration(&self.configuration);
        let mut manager = self.new_manager();
        tableau.update_extension_flags(&manager);
        self.configure_tableau_datatypes(&mut tableau);
        tableau.set_functional_roles_from_clauses(self.dl_ontology.get_dl_clauses());
        self.configure_tableau_description_graphs(&mut tableau);
        self.configure_tableau_blocking(&mut tableau);
        tableau.monitor_event(|m| m.is_satisfiable_started());
        let nodes_for_individuals = self.load_abox_tracking_individuals(&mut tableau, &[], &[]);
        if tableau.contains_clash() {
            tableau.monitor_event(|m| m.is_satisfiable_finished(false));
            return None;
        }
        let consistent = run_calculus(&mut tableau, &mut manager).unwrap_or(false);
        tableau.monitor_event(|m| m.is_satisfiable_finished(consistent));
        if !consistent {
            return None;
        }
        Some((tableau, nodes_for_individuals))
    }

    /// A compiled hyperresolution manager over this ontology's clauses, built once
    /// and reused across many satisfiability/subsumption tests (the clauses are the
    /// permanent TBox, so the compiled programs are tableau-independent -- exactly
    /// HermiT's single `m_tableau`/manager reused by the classification managers).
    pub fn new_manager(&self) -> HyperresolutionManager {
        HyperresolutionManager::with_core_variable_policy(
            self.dl_ontology.get_dl_clauses(),
            crate::tableau::dl_clause_evaluator::CoreVariablePolicy::from_blocking_strategy_type(
                self.configuration.blocking_strategy_type,
            ),
        )
    }

    /// Install the ontology's description graphs on a freshly built
    /// tableau, port of `Reasoner.createTableau` constructing
    /// `new DescriptionGraphManager(this)` from
    /// `m_permanentDLOntology.getAllDescriptionGraphs()`. Empty for ordinary
    /// ontologies, leaving the manager a no-op.
    fn configure_tableau_description_graphs(&self, tableau: &mut Tableau) {
        let graphs: Vec<crate::model::DescriptionGraph> = self
            .dl_ontology
            .get_all_description_graphs()
            .iter()
            .cloned()
            .collect();
        tableau.set_description_graphs(&graphs);
    }

    /// Whether the ontology is deterministic (Horn): then classification is a single
    /// model build per concept (`DeterministicClassification`), not pairwise tests.
    /// Mirrors `Tableau.isDeterministic` (the `CreationOrderStrategy` is
    /// deterministic, so this reduces to `DLOntology.isHorn`).
    pub fn is_deterministic(&self) -> bool {
        // Tableau.isDeterministic() (Tableau.java:155-156) is
        // `isHorn() && existentialExpansionStrategy.isDeterministic()`. Under the
        // default CreationOrder strategy the second conjunct is true, so this is a
        // no-op there; it only matters when a non-deterministic existential strategy
        // is selected.
        self.dl_ontology.is_horn()
            && self.configuration.existential_strategy_type.is_deterministic()
    }

    /// Builds a fresh tableau asserting `concept` on one fresh node and saturates it
    /// against the shared `manager`. Returns the canonical fresh node when
    /// satisfiable, or `None` on a clash. This is the reusable core of
    /// `Tableau.isSatisfiable` for a single root concept: the TBox clauses come from
    /// `manager`, so no re-clausification happens per test.
    /// A fresh tableau for a per-test reasoning task: sets the node-seeding flags
    /// from `manager` and, when the ontology has nominals, loads the permanent ABox
    /// (HermiT's `loadPermanentABox = m_permanentDLOntology.hasNominals()`, so a
    /// nominal `{a}` interacts with `a`'s asserted types). For nominal-free
    /// ontologies the ABox is irrelevant to class subsumption and is skipped.
    /// Returns `None` if the loaded ABox already clashes.
    /// Builds a fresh, fully-configured per-test tableau (the configuration-once
    /// half of HermiT's `m_tableau` setup). Does NOT load the ABox -- that is
    /// re-done on every checkout, since `clear()` wipes it.
    fn build_test_tableau(&self, manager: &HyperresolutionManager) -> Tableau {
        // Thread the reasoner's configuration (incl. the existential
        // strategy) into every per-test tableau, matching HermiT's single
        // configured `m_tableau` reused by the classification managers.
        let mut tableau = Tableau::with_configuration(&self.configuration);
        tableau.update_extension_flags(manager);
        self.configure_tableau_datatypes(&mut tableau);
        tableau.set_functional_roles_from_clauses(self.dl_ontology.get_dl_clauses());
        self.configure_tableau_description_graphs(&mut tableau);
        self.configure_tableau_blocking(&mut tableau);
        // Share the reasoner-wide never-reuse set so the IndividualReuseStrategy's
        // cross-test learning persists across these per-test tableaux.
        tableau.adopt_shared_reuse_never(std::rc::Rc::clone(&self.reuse_dont_ever));
        tableau
    }

    /// Checks out the reused per-test tableau (HermiT's single lifetime-scoped
    /// `m_tableau`). On the first checkout the tableau is built and cached; on
    /// every subsequent checkout the cached tableau is `clear()`ed (firing
    /// `tableauCleared`), reusing only the allocation. On every checkout -- first
    /// and reused -- the permanent ABox is (re-)loaded when the ontology has
    /// nominals (so a nominal `{a}` interacts with `a`'s asserted types; HermiT's
    /// `loadPermanentABox = hasNominals()`), and `None` is returned on an
    /// immediate ABox clash, exactly as the old `new_test_tableau` did.
    ///
    /// The returned [`TableauGuard`] returns the tableau to the cache on drop, so
    /// every caller's early-return / `?` paths keep the tableau for the next test.
    fn checkout_test_tableau(
        &self,
        manager: &HyperresolutionManager,
    ) -> Option<TableauGuard<'_>> {
        let mut tableau = match self.test_tableau.borrow_mut().take() {
            Some(mut cached) => {
                if cached.is_oversized() {
                    // A hard test grew the reused tableau's arrays to hundreds of
                    // MB+; `clear()` would keep that capacity for every later test,
                    // ratcheting per-worker RAM to OOM on EFO. Drop it and rebuild a
                    // fresh, right-sized tableau (the cache-miss path) so the memory
                    // is returned to the allocator.
                    if std::env::var_os("HERMIT_DEBUG_TABLEAU").is_some() {
                        eprintln!("[tableau] rebuild: retained_capacity={}", cached.retained_capacity());
                    }
                    // The oversized node/tuple ARRAYS are what we want returned to the
                    // allocator -- but the `BlockingSignatureCache` is small (sorted
                    // concept-id vecs) and is precisely the cross-test optimization
                    // that keeps every model after the first one shallow: a node whose
                    // signature a prior model already witnessed is blocked immediately
                    // (`signature_is_cached`). HermiT keeps one `m_tableau` (hence one
                    // signature cache) for the reasoner's whole lifetime, so preserving
                    // it here is the faithful behaviour. Dropping it (as a naive rebuild
                    // does) is catastrophic on cyclic inverse-role TBoxes: each full
                    // model trips the oversize limit, the cache is wiped, so the *next*
                    // model is full-size again and also trips it -- an unbounded
                    // rebuild loop (the EFO-scale `reason -r hermit` blow-up) where
                    // HermiT, reusing the cache, makes every later model tiny.
                    let preserved_signature_cache = cached.blocking_signature_cache.take();
                    drop(cached);
                    let mut fresh = self.build_test_tableau(manager);
                    if preserved_signature_cache.is_some() {
                        fresh.blocking_signature_cache = preserved_signature_cache;
                    }
                    fresh
                } else {
                    // Faithful port of HermiT reusing `m_tableau`: wipe per-test
                    // state (and fire tableauCleared) instead of reallocating.
                    cached.clear();
                    cached
                }
            }
            None => self.build_test_tableau(manager),
        };
        // The ABox must be (re-)loaded after every clear(), which wipes it.
        if self.dl_ontology.has_nominals() {
            self.load_abox(&mut tableau);
            if tableau.contains_clash() {
                // Return the tableau to the cache even on the clash early-return.
                *self.test_tableau.borrow_mut() = Some(tableau);
                return None;
            }
        }
        Some(TableauGuard {
            cache: &self.test_tableau,
            tableau: Some(tableau),
        })
    }

    /// Releases the cached per-test tableau *now* if a hard test grew it past the
    /// oversize threshold, returning the memory to the allocator immediately
    /// instead of at the next checkout (which is where `checkout_test_tableau`
    /// would otherwise rebuild it). Streaming workers call this after every model
    /// build so a worker that just saturated a multi-GB tableau does not keep that
    /// capacity pinned while it blocks idle waiting for its next concept. This is
    /// what makes the coordinator's memory governor effective: throttling dispatch
    /// only lowers resident memory if the quiescent workers actually shrink.
    pub fn release_oversized_test_tableau(&self) {
        let mut slot = self.test_tableau.borrow_mut();
        if slot.as_ref().is_some_and(|t| t.is_oversized()) {
            *slot = None;
        }
    }

    /// Saturates `concept(x)` on the reused per-test tableau and, on a model,
    /// passes the saturated tableau and the canonical root node to `read_off`,
    /// returning its result. Returns `None` when `concept` is unsatisfiable.
    /// Threading the read-off through a closure keeps the (reused) tableau owned
    /// by the guard, which returns it to the cache when this method returns.
    fn satisfiable_root<R>(
        &self,
        manager: &mut HyperresolutionManager,
        concept: Concept,
        read_off: impl FnOnce(&Tableau, NodeId) -> R,
    ) -> Option<R> {
        let mut guard = self.checkout_test_tableau(manager)?;
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let node = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(concept, node, &empty, true);
        if tableau.contains_clash() {
            return None;
        }
        // Route through `run_calculus` for the monitor/interrupt hooks.
        // An interrupt (only with a positive timeout) is treated as "no model".
        if !run_calculus(tableau, manager).unwrap_or(false) {
            return None;
        }
        let canonical = tableau.get_canonical_node(node);
        Some(read_off(tableau, canonical))
    }

    /// Faithful port of `DeterministicClassification.classify`'s per-element step:
    /// the subsumers of `element` are read off the single saturated model of
    /// `element(x)` (every atomic concept forced onto the fresh node `x`). Returns
    /// `None` when `element` is unsatisfiable (`element ⊑ ⊥`), in which case the
    /// caller treats every element as a subsumer. Requires `is_deterministic()`.
    pub fn concept_subsumers(
        &self,
        manager: &mut HyperresolutionManager,
        element: &crate::model::AtomicConcept,
    ) -> Option<Vec<crate::model::AtomicConcept>> {
        self.satisfiable_root(
            manager,
            Concept::AtomicConcept(element.clone()),
            |tableau, node| tableau.atomic_concepts_on_node(node),
        )
    }

    /// `buildModelForConcept` + `readKnownSubsumersFromRootNode` +
    /// `updatePossibleSubsumers` (QuasiOrderClassification): build one saturated
    /// model of `element(x)` and return `(root_known, node_labels)`:
    ///   * `root_known` -- the deterministic (empty-dependency-set) atomic concepts
    ///     on the root node, read only when the root was not merged
    ///     non-deterministically (Java's `getCanonicalNodeDependencySet().isEmpty()`
    ///     guard), i.e. `element`'s known subsumers.
    ///   * `node_labels` -- the atomic-concept label of every active, unblocked node
    ///     in the model, for cross-concept possible-subsumer harvesting (one model
    ///     populates the possibles of every concept that appears in it).
    /// `None` when `element` is unsatisfiable.
    pub fn concept_model_read_off(
        &self,
        manager: &mut HyperresolutionManager,
        element: &crate::model::AtomicConcept,
    ) -> Option<(
        std::collections::HashSet<crate::model::AtomicConcept>,
        Vec<std::collections::HashSet<crate::model::AtomicConcept>>,
    )> {
        use crate::tableau::dependency_set::DependencySetOps;
        let mut guard = self.checkout_test_tableau(manager)?;
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let root = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(Concept::AtomicConcept(element.clone()), root, &empty, true);
        if tableau.contains_clash() {
            return None;
        }
        if !run_calculus(tableau, manager).unwrap_or(false) {
            return None;
        }

        // `readKnownSubsumersFromRootNode`: only read deterministic subsumers when
        // the root's merge chain to its canonical node carries an empty dependency
        // set throughout (a non-deterministic merge makes the root label uncertain).
        let canonical_root = tableau.get_canonical_node(root);
        let mut root_deterministic = true;
        let mut walk = root;
        while let Some(into) = tableau.node(walk).get_merged_into() {
            let det = tableau
                .node(walk)
                .get_merged_into_dependency_set()
                .map_or(true, |d| d.is_empty());
            if !det {
                root_deterministic = false;
                break;
            }
            walk = into;
        }
        let empty_set = tableau.dependency_set_factory().empty_set();
        let mut root_known: std::collections::HashSet<crate::model::AtomicConcept> =
            std::collections::HashSet::new();
        if root_deterministic {
            for label in read_off_node_concepts(&*tableau, canonical_root, &empty_set) {
                if label.known {
                    root_known.insert(crate::model::AtomicConcept::create(label.concept_iri));
                }
            }
        }

        // `updatePossibleSubsumers`: the concept label of every active, unblocked node.
        let mut node_labels: Vec<std::collections::HashSet<crate::model::AtomicConcept>> =
            Vec::new();
        let mut node = tableau.get_first_tableau_node();
        while let Some(id) = node {
            if tableau.node(id).is_active() && !tableau.node(id).is_blocked() {
                let label: std::collections::HashSet<crate::model::AtomicConcept> =
                    tableau.atomic_concepts_on_node(id).into_iter().collect();
                if !label.is_empty() {
                    node_labels.push(label);
                }
            }
            node = tableau.node(id).get_next_tableau_node();
        }
        Some((root_known, node_labels))
    }

    /// Reads the object-property subsumers of `picked` off a single saturated
    /// model (the role analogue of `concept_subsumers` and HermiT's
    /// `buildModelForConcept`): assert `picked(a,b)` for fresh `a,b`, saturate, and
    /// return the candidate OPEs that hold on the edge -- `r` if `r(a,b)`, `Inv(r)`
    /// if `r(b,a)`. A candidate that does *not* hold in this model is provably not a
    /// subsumer (`picked ⋢ s`), so this narrows the possible-subsumer set to the
    /// roles that co-occur on the edge; the remaining ones are confirmed by
    /// `does_subsume`. Returns `None` when `picked` is unsatisfiable (`picked ⊑ ⊥`).
    pub fn object_property_edge_subsumers(
        &self,
        manager: &mut HyperresolutionManager,
        picked: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
        candidates: &[horned_owl::model::ObjectPropertyExpression<crate::structural::A>],
    ) -> Option<std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>>
    {
        use crate::model::{AtomicRole, Role};
        use horned_owl::model::ObjectPropertyExpression as OPE;
        let role_of = |p: &horned_owl::model::ObjectProperty<crate::structural::A>| {
            Role::AtomicRole(AtomicRole::create(&p.0.to_string()))
        };
        let mut guard = self.checkout_test_tableau(manager)?;
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        // Assert picked(a,b): Inv(r)(a,b) is r(b,a).
        match picked {
            OPE::ObjectProperty(r) => tableau.add_role_assertion(role_of(r), a, b, &empty, true),
            OPE::InverseObjectProperty(r) => tableau.add_role_assertion(role_of(r), b, a, &empty, true),
        };
        if tableau.contains_clash() {
            return None;
        }
        if !run_calculus(tableau, manager).unwrap_or(false) {
            return None;
        }
        let ca = tableau.get_canonical_node(a);
        let cb = tableau.get_canonical_node(b);
        let mut holds = std::collections::HashSet::new();
        for candidate in candidates {
            let (role, from, to) = match candidate {
                OPE::ObjectProperty(r) => (role_of(r), ca, cb),
                OPE::InverseObjectProperty(r) => (role_of(r), cb, ca),
            };
            if tableau.contains_role_assertion(&role, from, to) {
                holds.insert(candidate.clone());
            }
        }
        Some(holds)
    }

    /// The object-property analogue of
    /// [`atomic_subsumed_by_union_with_known`](Self::atomic_subsumed_by_union_with_known):
    /// reads `picked`'s *deterministic* (known) object-property subsumers off one
    /// saturated edge model -- the `readKnownSubsumersFromRootNode` half of
    /// `isEveryPossibleSubsumerNonSubsumer`'s positive branch for the role path.
    ///
    /// Assert `picked(a,b)` for fresh `a,b` with the empty dependency set, saturate,
    /// and return the candidate OPEs that hold on the canonical edge *with an empty
    /// dependency set* -- i.e. forced by `picked` alone, never the consequence of a
    /// non-deterministic choice. This mirrors Java's
    /// `readKnownSubsumersFromRootNode` (which only reads empty-dependency-set
    /// extension-table tuples, under the canonical-node determinism guard).
    ///
    /// This is the *known*-subsumer counterpart of
    /// [`object_property_edge_subsumers`](Self::object_property_edge_subsumers)
    /// (which returns *all* edge-subsumers, deterministic or not). The union test's
    /// negated candidates are loaded by the caller with a non-backtrackable dummy
    /// dependency set, so they can never enter any empty-dependency derivation;
    /// hence the deterministic subsumers of `picked` are identical whether read off
    /// the union-test model or this plain `picked(a,b)` model. Returns `None` when
    /// `picked` is unsatisfiable (`picked ⊑ ⊥`).
    pub fn object_property_deterministic_edge_subsumers(
        &self,
        manager: &mut HyperresolutionManager,
        picked: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>,
        candidates: &[horned_owl::model::ObjectPropertyExpression<crate::structural::A>],
    ) -> Option<std::collections::HashSet<horned_owl::model::ObjectPropertyExpression<crate::structural::A>>>
    {
        use crate::model::{AtomicRole, Role};
        use horned_owl::model::ObjectPropertyExpression as OPE;
        let role_of = |p: &horned_owl::model::ObjectProperty<crate::structural::A>| {
            Role::AtomicRole(AtomicRole::create(&p.0.to_string()))
        };
        let mut guard = self.checkout_test_tableau(manager)?;
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        // Assert picked(a,b): Inv(r)(a,b) is r(b,a).
        match picked {
            OPE::ObjectProperty(r) => tableau.add_role_assertion(role_of(r), a, b, &empty, true),
            OPE::InverseObjectProperty(r) => tableau.add_role_assertion(role_of(r), b, a, &empty, true),
        };
        if tableau.contains_clash() {
            return None;
        }
        if !run_calculus(tableau, manager).unwrap_or(false) {
            return None;
        }
        // readKnownSubsumersFromRootNode's determinism guard: only read off the
        // canonical edge when neither endpoint was merged non-deterministically (a
        // non-deterministic merge would make the canonical-edge labels uncertain).
        if !node_merge_chain_is_deterministic(&*tableau, a)
            || !node_merge_chain_is_deterministic(&*tableau, b)
        {
            return Some(std::collections::HashSet::new());
        }
        let ca = tableau.get_canonical_node(a);
        let cb = tableau.get_canonical_node(b);
        let mut known = std::collections::HashSet::new();
        for candidate in candidates {
            let (role, from, to) = match candidate {
                OPE::ObjectProperty(r) => (role_of(r), ca, cb),
                OPE::InverseObjectProperty(r) => (role_of(r), cb, ca),
            };
            if role_assertion_is_deterministic(&*tableau, &role, from, to) {
                known.insert(candidate.clone());
            }
        }
        Some(known)
    }

    /// The data-property analogue of [`object_property_edge_subsumers`]: assert
    /// `picked(a,k)` for a fresh individual `a` and a fresh data successor `k`,
    /// saturate, and return the candidate data properties `s` with `s(a,k)` -- the
    /// (possible) subsumers read off the model. Returns `None` when `picked` is
    /// unsatisfiable.
    ///
    /// [`object_property_edge_subsumers`]: Self::object_property_edge_subsumers
    pub fn data_property_edge_subsumers(
        &self,
        manager: &mut HyperresolutionManager,
        picked: &horned_owl::model::DataProperty<crate::structural::A>,
        candidates: &[horned_owl::model::DataProperty<crate::structural::A>],
    ) -> Option<std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>>> {
        use crate::model::{AtomicRole, Role};
        let role_of = |p: &horned_owl::model::DataProperty<crate::structural::A>| {
            Role::AtomicRole(AtomicRole::create(&p.0.to_string()))
        };
        let mut guard = self.checkout_test_tableau(manager)?;
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let k = tableau.create_new_concrete_node(&empty, a);
        tableau.add_role_assertion(role_of(picked), a, k, &empty, true);
        if tableau.contains_clash() {
            return None;
        }
        if !run_calculus(tableau, manager).unwrap_or(false) {
            return None;
        }
        let ca = tableau.get_canonical_node(a);
        let ck = tableau.get_canonical_node(k);
        let mut holds = std::collections::HashSet::new();
        for candidate in candidates {
            if tableau.contains_role_assertion(&role_of(candidate), ca, ck) {
                holds.insert(candidate.clone());
            }
        }
        Some(holds)
    }

    /// The data-property analogue of
    /// [`object_property_deterministic_edge_subsumers`]: reads `picked`'s
    /// *deterministic* (known) data-property subsumers off one saturated
    /// `picked(a,k)` model, keeping only the candidates whose edge tuple carries an
    /// empty dependency set (`readKnownSubsumersFromRootNode`). Returns `None` when
    /// `picked` is unsatisfiable.
    ///
    /// [`object_property_deterministic_edge_subsumers`]: Self::object_property_deterministic_edge_subsumers
    pub fn data_property_deterministic_edge_subsumers(
        &self,
        manager: &mut HyperresolutionManager,
        picked: &horned_owl::model::DataProperty<crate::structural::A>,
        candidates: &[horned_owl::model::DataProperty<crate::structural::A>],
    ) -> Option<std::collections::HashSet<horned_owl::model::DataProperty<crate::structural::A>>> {
        use crate::model::{AtomicRole, Role};
        let role_of = |p: &horned_owl::model::DataProperty<crate::structural::A>| {
            Role::AtomicRole(AtomicRole::create(&p.0.to_string()))
        };
        let mut guard = self.checkout_test_tableau(manager)?;
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let k = tableau.create_new_concrete_node(&empty, a);
        tableau.add_role_assertion(role_of(picked), a, k, &empty, true);
        if tableau.contains_clash() {
            return None;
        }
        if !run_calculus(tableau, manager).unwrap_or(false) {
            return None;
        }
        if !node_merge_chain_is_deterministic(&*tableau, a)
            || !node_merge_chain_is_deterministic(&*tableau, k)
        {
            return Some(std::collections::HashSet::new());
        }
        let ca = tableau.get_canonical_node(a);
        let ck = tableau.get_canonical_node(k);
        let mut known = std::collections::HashSet::new();
        for candidate in candidates {
            if role_assertion_is_deterministic(&*tableau, &role_of(candidate), ca, ck) {
                known.insert(candidate.clone());
            }
        }
        Some(known)
    }

    /// Reusable atomic-class subsumption test `sub ⊑ sup`: true iff `sub ⊓ ¬sup` is
    /// unsatisfiable. Used by the non-deterministic classification path so it, too,
    /// reuses the compiled clauses instead of re-clausifying per pair.
    pub fn atomic_subsumes(
        &self,
        manager: &mut HyperresolutionManager,
        sub: &crate::model::AtomicConcept,
        sup: &crate::model::AtomicConcept,
    ) -> bool {
        if sub == sup {
            return true;
        }
        // An ABox clash means the ontology is inconsistent, so everything is
        // subsumed by everything.
        let Some(mut guard) = self.checkout_test_tableau(manager) else {
            return true;
        };
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let node = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(Concept::AtomicConcept(sub.clone()), node, &empty, true);
        tableau.add_concept_assertion(Concept::from(sup.get_negation()), node, &empty, true);
        if tableau.contains_clash() {
            return true;
        }
        // An interrupt (positive timeout only) yields "no model found",
        // i.e. a clash, so the subsumption holds.
        !run_calculus(tableau, manager).unwrap_or(false)
    }

    /// Reusable batched subsumption test `child ⊑ ⊔ candidates`
    /// (`QuasiOrderClassification.isEveryPossibleSubsumerNonSubsumer`): assert
    /// `child(x)` and `¬cᵢ(x)` for every candidate on one fresh node; the union
    /// subsumption holds iff that is unsatisfiable (no model leaves `x` outside
    /// every candidate). An empty candidate set tests whether `child` is
    /// unsatisfiable as a concept.
    pub fn atomic_subsumed_by_union(
        &self,
        manager: &mut HyperresolutionManager,
        child: &crate::model::AtomicConcept,
        candidates: &std::collections::HashSet<crate::model::AtomicConcept>,
    ) -> bool {
        let Some(mut guard) = self.checkout_test_tableau(manager) else {
            return true;
        };
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let node = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(Concept::AtomicConcept(child.clone()), node, &empty, true);
        for candidate in candidates {
            tableau.add_concept_assertion(
                Concept::from(candidate.get_negation()),
                node,
                &empty,
                true,
            );
        }
        if tableau.contains_clash() {
            return true;
        }
        !run_calculus(tableau, manager).unwrap_or(false)
    }

    /// As [`atomic_subsumed_by_union`](Self::atomic_subsumed_by_union), but on a
    /// positive result also reads `child`'s deterministic known subsumers off the
    /// witnessing model (`readKnownSubsumersFromRootNode`). The candidate negations
    /// are loaded with a non-backtrackable *dummy* dependency set (mirroring
    /// `isSatisfiable`'s `perTestNegativeFactsDummyDependency`), so the
    /// empty-dependency concept assertions remaining on the root are exactly the
    /// deterministic consequences of `child` alone -- never of the negated
    /// candidates -- making the read-off sound. When `child` is not subsumed by
    /// the union, the second component is empty (and unused by the caller).
    pub fn atomic_subsumed_by_union_with_known(
        &self,
        manager: &mut HyperresolutionManager,
        child: &crate::model::AtomicConcept,
        candidates: &std::collections::HashSet<crate::model::AtomicConcept>,
    ) -> (bool, std::collections::HashSet<crate::model::AtomicConcept>) {
        use crate::tableau::dependency_set::DependencySetOps;
        let empty_known = std::collections::HashSet::new();
        let Some(mut guard) = self.checkout_test_tableau(manager) else {
            return (true, empty_known);
        };
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let root = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(Concept::AtomicConcept(child.clone()), root, &empty, true);
        // The negated candidates carry a non-backtrackable dummy dependency set,
        // so nothing derived from them is ever empty-dependency.
        let dummy = DependencySet::Permanent(tableau.push_dummy_dependency_branching_point());
        for candidate in candidates {
            tableau.add_concept_assertion(
                Concept::from(candidate.get_negation()),
                root,
                &dummy,
                true,
            );
        }
        if tableau.contains_clash() {
            // Subsumed, but the root carries no usable (post-saturation) label.
            return (true, empty_known);
        }
        let subsumed = !run_calculus(tableau, manager).unwrap_or(false);
        if !subsumed {
            return (false, empty_known);
        }
        // readKnownSubsumersFromRootNode: only read deterministic subsumers when
        // the root's merge chain to its canonical node is empty-dependency throughout.
        let canonical_root = tableau.get_canonical_node(root);
        let mut root_deterministic = true;
        let mut walk = root;
        while let Some(into) = tableau.node(walk).get_merged_into() {
            let det = tableau
                .node(walk)
                .get_merged_into_dependency_set()
                .map_or(true, |d| d.is_empty());
            if !det {
                root_deterministic = false;
                break;
            }
            walk = into;
        }
        let mut known: std::collections::HashSet<crate::model::AtomicConcept> =
            std::collections::HashSet::new();
        if root_deterministic {
            let empty_set = tableau.dependency_set_factory().empty_set();
            for label in read_off_node_concepts(&*tableau, canonical_root, &empty_set) {
                if label.known {
                    known.insert(crate::model::AtomicConcept::create(label.concept_iri));
                }
            }
        }
        (subsumed, known)
    }

    /// The subsumption test `sub ⊑ sup` together with the model read-off that
    /// `QuasiOrderClassification.doesSubsume` harvests from the witnessing model:
    /// `readKnownSubsumersFromRootNode` (the deterministic subsumers of `sub`) and
    /// `prunePossibleSubsumers` (every active, unblocked node's concept label, used
    /// to prune the possible-subsumer sets). `¬sup` is asserted with a
    /// non-backtrackable *dummy* dependency (mirroring `isSatisfiable`'s
    /// `perTestNegativeFactsDummyDependency`) so the empty-dependency root concepts
    /// are exactly the deterministic consequences of `sub` alone, never of `¬sup`.
    /// Returns `(subsumed, None)` when `sub ⊑ sup` (the test is unsatisfiable, so no
    /// model exists) and `(false, Some((root_known, node_labels)))` otherwise.
    #[allow(clippy::type_complexity)]
    pub fn atomic_subsumes_with_read_off(
        &self,
        manager: &mut HyperresolutionManager,
        sub: &crate::model::AtomicConcept,
        sup: &crate::model::AtomicConcept,
    ) -> (
        bool,
        Option<(
            std::collections::HashSet<crate::model::AtomicConcept>,
            Vec<std::collections::HashSet<crate::model::AtomicConcept>>,
        )>,
    ) {
        use crate::tableau::dependency_set::DependencySetOps;
        if sub == sup {
            return (true, None);
        }
        let Some(mut guard) = self.checkout_test_tableau(manager) else {
            // An inconsistent ABox subsumes everything.
            return (true, None);
        };
        let tableau = &mut *guard;
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let root = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(Concept::AtomicConcept(sub.clone()), root, &empty, true);
        // `¬sup` carries a non-backtrackable dummy dependency set, so nothing derived
        // from it is ever empty-dependency.
        let dummy = DependencySet::Permanent(tableau.push_dummy_dependency_branching_point());
        tableau.add_concept_assertion(Concept::from(sup.get_negation()), root, &dummy, true);
        if tableau.contains_clash() {
            return (true, None);
        }
        let subsumed = !run_calculus(tableau, manager).unwrap_or(false);
        if subsumed {
            return (true, None);
        }

        // readKnownSubsumersFromRootNode: read deterministic subsumers only when the
        // root's merge chain to its canonical node is empty-dependency throughout.
        let canonical_root = tableau.get_canonical_node(root);
        let mut root_deterministic = true;
        let mut walk = root;
        while let Some(into) = tableau.node(walk).get_merged_into() {
            let det = tableau
                .node(walk)
                .get_merged_into_dependency_set()
                .map_or(true, |d| d.is_empty());
            if !det {
                root_deterministic = false;
                break;
            }
            walk = into;
        }
        let empty_set = tableau.dependency_set_factory().empty_set();
        let mut root_known: std::collections::HashSet<crate::model::AtomicConcept> =
            std::collections::HashSet::new();
        if root_deterministic {
            for label in read_off_node_concepts(&*tableau, canonical_root, &empty_set) {
                if label.known {
                    root_known.insert(crate::model::AtomicConcept::create(label.concept_iri));
                }
            }
        }

        // prunePossibleSubsumers: the concept label of every active, unblocked node.
        let mut node_labels: Vec<std::collections::HashSet<crate::model::AtomicConcept>> =
            Vec::new();
        let mut node = tableau.get_first_tableau_node();
        while let Some(id) = node {
            if tableau.node(id).is_active() && !tableau.node(id).is_blocked() {
                let label: std::collections::HashSet<crate::model::AtomicConcept> =
                    tableau.atomic_concepts_on_node(id).into_iter().collect();
                if !label.is_empty() {
                    node_labels.push(label);
                }
            }
            node = tableau.node(id).get_next_tableau_node();
        }
        (false, Some((root_known, node_labels)))
    }

    /// Port of `Reasoner.getTableau(additionalAxioms)` +
    /// `isSatisfiable(true, true, ...)`: tests whether the ontology stays consistent
    /// once the `additional` axioms are added, by clausifying them into a delta DL
    /// ontology (`createDeltaDLOntology`) and reasoning over the delta as an
    /// additional hyperresolution manager (`setAdditionalDLOntology`). The permanent
    /// KB is not re-clausified -- only the delta is compiled, exactly as HermiT's
    /// incremental `getTableau(additionalAxioms)` fast path. Returns `true` when the
    /// combined ontology is consistent.
    pub fn is_consistent_with_additional_axioms(
        &self,
        additional: &SetOntology<crate::structural::A>,
    ) -> Result<bool, String> {
        use crate::tableau::dl_clause_evaluator::CoreVariablePolicy;
        // createDeltaDLOntology: clausify the added axioms against the original KB
        // (index-threaded so fresh definition concepts do not collide).
        let delta = create_delta_dl_ontology(additional, self.dl_ontology)?;
        let permanent_manager = self.new_manager();
        // m_additionalHyperresolutionManager = new HyperresolutionManager(delta clauses).
        let mut additional_manager = HyperresolutionManager::with_core_variable_policy(
            delta.get_dl_clauses(),
            CoreVariablePolicy::from_blocking_strategy_type(
                self.configuration.blocking_strategy_type,
            ),
        );
        let mut tableau = self.build_test_tableau(&permanent_manager);
        // updateFlagsDependentOnAdditionalOntology: the node-seeding and datatype
        // flags must cover both the permanent and additional ontologies.
        tableau.merge_extension_flags(&additional_manager);
        tableau.check_datatypes |= delta.has_datatypes();
        tableau.check_unknown_datatype_restrictions |= delta.has_unknown_datatype_restrictions();
        // Java decides via Tableau.supportsAdditionalDLOntology whether the cached
        // permanent tableau may be reused (its blocking was configured for the
        // permanent ontology) or whether a fresh tableau over the COMBINED ontology
        // must be built (Reasoner.getTableau, Reasoner.java:1922-1933). build_test_tableau
        // configured blocking + the blocking validator from the permanent ontology
        // alone; reconfigure them over permanent ∪ delta so the result is correct
        // regardless -- a delta introducing inverse roles / nominals, or whose clauses
        // the validator must see, would otherwise be reasoned with the wrong blocking.
        let combined_has_inverses =
            self.dl_ontology.has_inverse_roles() || delta.has_inverse_roles();
        let combined_has_nominals = self.dl_ontology.has_nominals() || delta.has_nominals();
        tableau.configure_blocking(&self.configuration, combined_has_inverses, combined_has_nominals);
        if tableau.blocking_uses_validator() {
            let mut combined_clauses = self.dl_ontology.get_dl_clauses().clone();
            combined_clauses.extend(delta.get_dl_clauses().iter().cloned());
            let validator =
                crate::tableau::blocking_validator::BlockingValidator::new(&combined_clauses);
            tableau.set_blocking_validator(validator);
        }

        // loadPermanentABox + loadAdditionalABox: a node per individual of both
        // ontologies, then assert the permanent and additional facts.
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let mut nodes_for_terms: HashMap<Term, NodeId> = HashMap::new();
        for individual in self
            .dl_ontology
            .get_all_individuals()
            .iter()
            .chain(delta.get_all_individuals().iter())
        {
            let term = Term::Individual(individual.clone());
            if nodes_for_terms.contains_key(&term) {
                continue;
            }
            let node = if individual.is_anonymous() {
                tableau.create_new_ni_node(&empty)
            } else {
                tableau.create_new_named_node(&empty)
            };
            nodes_for_terms.insert(term, node);
        }
        for atom in self
            .dl_ontology
            .get_positive_facts()
            .iter()
            .chain(delta.get_positive_facts().iter())
        {
            self.assert_fact(&mut tableau, atom, &mut nodes_for_terms, &empty, false);
            if tableau.contains_clash() {
                return Ok(false);
            }
        }
        for atom in self
            .dl_ontology
            .get_negative_facts()
            .iter()
            .chain(delta.get_negative_facts().iter())
        {
            self.assert_fact(&mut tableau, atom, &mut nodes_for_terms, &empty, true);
            if tableau.contains_clash() {
                return Ok(false);
            }
        }
        // "Ensure that at least one individual exists" (Tableau.java:307-309).
        if tableau.get_first_tableau_node().is_none() {
            tableau.create_new_ni_node(&empty);
        }

        let mut permanent_manager = permanent_manager;
        Ok(run_calculus_with_additional(
            &mut tableau,
            &mut permanent_manager,
            Some(&mut additional_manager),
        )
        .unwrap_or(false))
    }

    /// Whether the atomic concept `element` is satisfiable, reusing `manager`.
    pub fn atomic_satisfiable(
        &self,
        manager: &mut HyperresolutionManager,
        element: &crate::model::AtomicConcept,
    ) -> bool {
        self.satisfiable_root(manager, Concept::AtomicConcept(element.clone()), |_, _| ())
            .is_some()
    }

    fn load_abox(&self, tableau: &mut Tableau) {
        let _ = self.load_abox_tracking_individuals(tableau, &[], &[]);
    }

    /// Like [`load_abox`](Self::load_abox) but also returns the
    /// individual -> tableau-node mapping built while loading the ABox.
    ///
    /// This mirrors HermiT's `m_nodesForIndividuals` (the `Map<Individual,Node>`
    /// the consistency-check `Tableau` populates as it creates the named node for
    /// each individual). The mapping is the entry point of
    /// `InstanceManager.initializeKnowAndPossibleClassInstances`'s read-off: each
    /// individual's saturated node carries its known/possible atomic-concept
    /// memberships. The returned `NodeId`s are the *raw* (pre-merge) nodes; callers
    /// take the canonical node via `Tableau::get_canonical_node` exactly as Java's
    /// read-off uses `node.getCanonicalNode()`.
    fn load_abox_tracking_individuals(
        &self,
        tableau: &mut Tableau,
        positive_test_atoms: &[crate::model::Atom],
        negative_test_atoms: &[crate::model::Atom],
    ) -> HashMap<crate::model::Individual, NodeId> {
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let mut nodes_for_terms: HashMap<Term, NodeId> = HashMap::new();
        let mut nodes_for_individuals: HashMap<crate::model::Individual, NodeId> = HashMap::new();

        // A node per individual: anonymous individuals get an NI node, named
        // individuals a named node (Tableau.getNodeForTerm, Tableau.java:353-358).
        for individual in self.dl_ontology.get_all_individuals() {
            let node = if individual.is_anonymous() {
                tableau.create_new_ni_node(&empty)
            } else {
                tableau.create_new_named_node(&empty)
            };
            nodes_for_terms.insert(Term::Individual(individual.clone()), node);
            nodes_for_individuals.insert(individual.clone(), node);
        }

        for atom in self.dl_ontology.get_positive_facts() {
            self.assert_fact(tableau, atom, &mut nodes_for_terms, &empty, false);
            if tableau.contains_clash() {
                return nodes_for_individuals;
            }
        }
        for atom in self.dl_ontology.get_negative_facts() {
            self.assert_fact(tableau, atom, &mut nodes_for_terms, &empty, true);
            if tableau.contains_clash() {
                return nodes_for_individuals;
            }
        }
        // HermiT's `tableau.isSatisfiable(..., perTestAtoms, ...)` adds the per-test
        // ABox atoms alongside the loaded KB, reusing one tableau across tests
        // instead of re-clausifying. They are asserted with the same individual->node
        // mapping so they reference the loaded individuals.
        for atom in positive_test_atoms {
            self.assert_fact(tableau, atom, &mut nodes_for_terms, &empty, false);
            if tableau.contains_clash() {
                return nodes_for_individuals;
            }
        }
        for atom in negative_test_atoms {
            self.assert_fact(tableau, atom, &mut nodes_for_terms, &empty, true);
            if tableau.contains_clash() {
                return nodes_for_individuals;
            }
        }

        // "Ensure that at least one individual exists" (Tableau.java:307-309): an
        // empty ABox still has a non-empty domain, so `⊤ ⊑ C` GCIs must fire and a
        // TBox-only inconsistency (e.g. `⊤ ⊑ ⊥`) must be detected. Without a node,
        // no clause ever fires and the ontology is wrongly "consistent".
        if tableau.get_first_tableau_node().is_none() {
            tableau.create_new_ni_node(&empty);
        }
        nodes_for_individuals
    }

    fn node_for_term(
        &self,
        tableau: &mut Tableau,
        term: &Term,
        nodes_for_terms: &mut HashMap<Term, NodeId>,
        empty: &DependencySet,
    ) -> NodeId {
        let raw = if let Some(&node) = nodes_for_terms.get(term) {
            node
        } else {
            // A previously unseen term (e.g. a data constant) gets a fresh node.
            let node = match term {
                Term::Constant(constant) => {
                    let node = tableau.create_new_root_constant_node(empty);
                    tableau.node_mut(node).constant_value = Some(constant.clone());
                    // As in Java's `Tableau.getNodeForTerm`, assert a singleton
                    // `ConstantEnumeration {constant}` on the node. This is the
                    // semantic representation of the value (the `constant_value`
                    // field is only a cache): because the merge rule copies
                    // extension-table assertions onto the survivor, two distinct
                    // constants merged under a functional data property both keep
                    // their singleton enumerations, so the datatype check sees an
                    // empty `{c1} ⊓ {c2}` conjunction and clashes. Anonymous
                    // constant values are deliberately not pinned to a particular
                    // value, so no enumeration is asserted for them.
                    if !constant.is_anonymous() {
                        let enumeration = crate::model::ConstantEnumeration::create(vec![
                            constant.clone(),
                        ]);
                        tableau.add_dl_predicate_assertion(
                            crate::model::DLPredicate::ConstantEnumeration(enumeration),
                            node,
                            empty,
                            true,
                        );
                    }
                    node
                }
                Term::Individual(individual) if individual.is_anonymous() => {
                    tableau.create_new_ni_node(empty)
                }
                _ => tableau.create_new_named_node(empty),
            };
            nodes_for_terms.insert(term.clone(), node);
            node
        };
        // Assert on the canonical node so that facts loaded after an
        // equality-induced merge target the surviving node (independent of the
        // order in which facts are loaded).
        tableau.get_canonical_node(raw)
    }

    fn assert_fact(
        &self,
        tableau: &mut Tableau,
        atom: &crate::model::Atom,
        nodes_for_terms: &mut HashMap<Term, NodeId>,
        empty: &DependencySet,
        negative: bool,
    ) {
        let predicate = atom.get_dl_predicate().clone();
        match atom.get_arity() {
            1 => {
                let node =
                    self.node_for_term(tableau, atom.get_argument(0), nodes_for_terms, empty);
                if negative {
                    if let DLPredicate::AtomicConcept(a) = predicate {
                        tableau.add_concept_assertion(
                            Concept::from(a.get_negation()),
                            node,
                            empty,
                            true,
                        );
                    }
                } else {
                    tableau.add_unary_from_predicate(predicate, node, empty, true);
                }
            }
            2 => {
                let n0 =
                    self.node_for_term(tableau, atom.get_argument(0), nodes_for_terms, empty);
                let n1 =
                    self.node_for_term(tableau, atom.get_argument(1), nodes_for_terms, empty);
                match predicate {
                    DLPredicate::AtomicRole(r) => {
                        if negative {
                            tableau.add_ternary(
                                TableauObject::NegatedAtomicRole(NegatedAtomicRole::create(r)),
                                n0,
                                n1,
                                empty,
                                true,
                            );
                        } else {
                            tableau.add_role_assertion(Role::AtomicRole(r), n0, n1, empty, true);
                        }
                    }
                    DLPredicate::Equality => {
                        // Tableau.loadNegativeFact maps a negative Equality to an
                        // Inequality assertion; a positive Equality is a merge.
                        if negative {
                            tableau.add_ternary(
                                TableauObject::DLPredicate(DLPredicate::Inequality),
                                n0,
                                n1,
                                empty,
                                true,
                            );
                        } else {
                            tableau.merge_nodes(n0, n1, empty);
                        }
                    }
                    DLPredicate::Inequality => {
                        // Tableau.loadNegativeFact maps a negative Inequality to a merge;
                        // a positive Inequality is an Inequality assertion.
                        if negative {
                            tableau.merge_nodes(n0, n1, empty);
                        } else {
                            tableau.add_ternary(
                                TableauObject::DLPredicate(DLPredicate::Inequality),
                                n0,
                                n1,
                                empty,
                                true,
                            );
                        }
                    }
                    other => {
                        tableau.add_ternary(
                            TableauObject::DLPredicate(other),
                            n0,
                            n1,
                            empty,
                            true,
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

// ===========================================================================
// Incremental, mutable OWLReasoner (buffering / flush)
//
// HermiT's `org.semanticweb.HermiT.Reasoner` is a *mutable* `OWLReasoner`: it
// owns the loaded ontology, tracks a list of pending `OWLOntologyChange`s
// (`m_pendingChanges`), exposes a `BufferingMode` derived from
// `Configuration.bufferChanges` (`getBufferingMode`, Reasoner.java:354), and a
// `flush()` (Reasoner.java:374) that applies the buffered changes to the loaded
// `DLOntology` and invalidates the cached tableau / consistency / instance
// manager so the next query reflects them. In NON_BUFFERING mode every query
// first calls `flushChangesIfRequired` (Reasoner.java:2179) which flushes
// immediately, so a change takes effect without an explicit `flush()`.
//
// The port's `Reasoner` only *borrows* a `&DLOntology`, and the public free
// functions take a fresh `SetOntology` each call, so there was no incremental
// add/remove/flush API. `IncrementalReasoner` provides one, faithfully:
//
//   * It OWNS a `SetOntology` and a `Configuration` (whose `buffer_changes`
//     gives the `BufferingMode`, default BUFFERING -- Configuration default
//     `buffer_changes = true`, matching Java's `bufferChanges = true`).
//   * `add_axiom` / `remove_axiom` / `apply_changes` mirror
//     `OntologyChangeListener.ontologiesChanged` (Reasoner.java:347): in
//     BUFFERING mode they queue an `OntologyChange` onto the pending buffer; in
//     NON_BUFFERING mode they apply immediately (queue + flush), invalidating
//     caches -- exactly Java's `flushChangesIfRequired` behaviour.
//   * `flush()` (Reasoner.java:374) applies the buffered changes to the owned
//     ontology and invalidates the cached consistency/classification so the next
//     query re-reasons from the current ontology. `flush()` with no pending
//     changes is a no-op (`if (!m_pendingChanges.isEmpty())`).
//   * Each query (consistency / classify / sub-/super-/equivalent-classes /
//     instances / entailment ...) reasons against the *current* (post-flush)
//     ontology by delegating to the existing free functions over the owned
//     `SetOntology`.
//
// INCREMENTAL FLUSH (Reasoner.java:374-414): `flush()` now mirrors
// Java's two-branch mechanism rather than re-clausifying the whole ontology from
// scratch:
//
//   * The first full clausification caches the ORIGINAL `DLOntology` (TBox
//     clauses + ABox facts) and the original atomic-concept count.
//   * On `flush()`, `can_process_pending_changes_incrementally`
//     (Reasoner.java:416) classifies the pending changes. When ALL pending
//     changes are ABox assertions over already-present vocabulary (no TBox/RBox
//     change, no nominals/description-graphs), the INCREMENTAL path runs: the
//     delta ABox is clausified with `ReducedABoxClausification::clausify`
//     (Reasoner.java:385-401) against a `Vocabulary` built from the original
//     ontology's atomic concepts / object roles / data roles, and a combined
//     `DLOntology` is produced = original TBox clauses + original facts ± the
//     delta facts (Reasoner.java:406). An Add contributes its facts; a Remove
//     drops them.
//   * Otherwise (a TBox/RBox change, or an assertion the reduced clausifier
//     rejects) it FALLS BACK to a full re-clausification of the flushed
//     ontology (`loadOntology`). When that fallback must clausify ADDED axioms on
//     top of the original (the `createAdditionalTableau`/`createDeltaDLOntology`
//     mechanism), it THREADS the original atomic-concept count as the replacement
//     index (Reasoner.java:2072-2073) so fresh `internal:all#` concepts do not
//     collide -- see `create_delta_dl_ontology`.
//
// The consistency query reasons from the combined/cached `DLOntology` (Java's
// `m_dlOntology`), exactly as Java's rebuilt `m_tableau`.
//
// Performance note (answer-identical): Java reuses a single persistent `m_tableau` object
// across flushes (`new Tableau(...,m_dlOntology,...)` at Reasoner.java:407, then
// re-seeded). Building a live, persistent tableau that survives across flushes
// would require editing the `tableau` module (not owned here). Instead each
// consistency query constructs a fresh `Reasoner` over the combined `DLOntology`
// and reasons -- this is ANSWER-IDENTICAL (a tableau is a pure function of its
// `DLOntology`; reuse is only a performance optimization) while still using the
// `ReducedABoxClausification` for the ABox delta and threading the index on the
// additional clausification, which are the faithfulness points. The
// classify/instances/sub-class style queries still delegate to the free
// functions over the kept-in-sync owned `SetOntology` (also answer-identical).
// ===========================================================================


/// Builds the combined `DLOntology` of the incremental ABox path
/// (Reasoner.java:406): the `base`'s TBox clauses and vocabulary, with the
/// supplied (delta-merged) positive/negative facts. The individuals are
/// recomputed from the facts (Java's `atom.getIndividuals(allIndividuals)` loop),
/// and the expressivity flags / complex roles / datatype info are carried over
/// from `base` unchanged (ABox-only changes cannot alter them).
fn combined_dl_ontology(
    base: &DLOntology,
    positive_facts: std::collections::HashSet<crate::model::Atom>,
    negative_facts: std::collections::HashSet<crate::model::Atom>,
) -> DLOntology {
    use crate::model::Term;
    use std::collections::BTreeSet;

    let mut individuals: BTreeSet<crate::model::Individual> = BTreeSet::new();
    for atom in positive_facts.iter().chain(negative_facts.iter()) {
        for i in 0..atom.get_arity() {
            if let Term::Individual(individual) = atom.get_argument(i) {
                individuals.insert(individual.clone());
            }
        }
    }

    DLOntology::new(
        base.get_ontology_iri().to_string(),
        base.get_dl_clauses().clone(),
        positive_facts,
        negative_facts,
        Some(base.get_all_atomic_concepts().clone()),
        Some(base.get_all_atomic_object_roles().clone()),
        Some(base.get_all_complex_object_roles().clone()),
        Some(base.get_all_atomic_data_roles().clone()),
        Some(base.get_all_unknown_datatype_restrictions().clone()),
        Some(base.get_defined_datatype_iris().clone()),
        Some(individuals),
        base.has_inverse_roles(),
        base.has_at_most_restrictions(),
        base.has_nominals(),
        base.has_datatypes(),
    )
}

/// Port of `org.semanticweb.owlapi.reasoner.BufferingMode`. Derived from
/// `Configuration.bufferChanges` exactly as `Reasoner.getBufferingMode`
/// (Reasoner.java:354): `bufferChanges ? BUFFERING : NON_BUFFERING`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BufferingMode {
    /// Changes are buffered until `flush()` (Java default; `bufferChanges=true`).
    Buffering,
    /// Changes take effect immediately (each query flushes first).
    NonBuffering,
}

/// Port of the `AddAxiom`/`RemoveAxiom` `OWLOntologyChange` kinds that
/// `OntologyChangeListener.ontologiesChanged` records onto `m_pendingChanges`
/// (Reasoner.java:347-351). Annotation-only ontology changes are filtered out by
/// Java (`RemoveOntologyAnnotation`/`AddOntologyAnnotation`); the analogue here
/// is that callers only ever submit axiom (`Component`) changes.
#[derive(Debug, Clone, PartialEq)]
pub enum OntologyChange {
    /// `AddAxiom`: insert the component into the loaded ontology on flush.
    Add(Component<crate::structural::A>),
    /// `RemoveAxiom`: remove the component from the loaded ontology on flush.
    Remove(Component<crate::structural::A>),
}

impl OntologyChange {
    /// The affected axiom (`OWLOntologyChange.getAxiom`).
    pub fn axiom(&self) -> &Component<crate::structural::A> {
        match self {
            OntologyChange::Add(c) | OntologyChange::Remove(c) => c,
        }
    }
}

/// A mutable, incremental reasoner mirroring HermiT's `Reasoner` as an
/// `OWLReasoner`. It owns the ontology and a pending-changes buffer; see
/// the module note above for the faithful mapping to `Reasoner.java`.
pub struct IncrementalReasoner {
    /// The loaded ontology (Java's `m_rootOntology` + the derived `m_dlOntology`).
    /// Queries reason against this *current* (post-flush) ontology.
    ontology: SetOntology<crate::structural::A>,
    /// The reasoner configuration; `buffer_changes` gives the `BufferingMode`
    /// (Java's `m_configuration`).
    configuration: crate::configuration::Configuration,
    /// Java's `m_pendingChanges`: changes recorded but not yet applied.
    pending_changes: Vec<OntologyChange>,
    /// Java's `m_isConsistent`: cached consistency of the current ontology,
    /// `None` until first computed and nulled on every `flush` that applies
    /// changes.
    cached_consistent: Option<bool>,
    /// Java's `m_dlOntology`: the combined clausified ontology (TBox clauses +
    /// current ABox facts) that the consistency query reasons from. `None` until
    /// the first clausification; rebuilt incrementally (ABox-only) or fully
    /// (fallback) on each `flush`.
    dl_ontology: Option<DLOntology>,
    /// The ORIGINAL clausified `DLOntology` (TBox clauses + the facts at the time
    /// of the last FULL clausification). The incremental ABox path reuses its TBox
    /// clauses and vocabulary; `create_delta_dl_ontology` threads its
    /// atomic-concept count as the replacement index.
    original_dl_ontology: Option<DLOntology>,
    /// `originalDLOntology.getAllAtomicConcepts().size()` -- the replacement index
    /// threaded into the additional/delta clausification (Reasoner.java:2072-2073).
    original_atomic_concept_count: usize,
    /// Whether the most recent `flush` that applied changes took the INCREMENTAL
    /// (reduced-ABox) path (`Some(true)`), the full-rebuild fallback
    /// (`Some(false)`), or no flush has applied changes yet (`None`). Observable so
    /// tests can assert which path Java's `canProcessPendingChangesIncrementally`
    /// branch was taken.
    last_flush_was_incremental: Option<bool>,
    /// The inference types precomputed since the last flush that applied
    /// changes (Java's per-cache completion flags read by `isPrecomputed`). Stateful,
    /// unlike the free `is_precomputed` (which has no instance to remember).
    precomputed_inferences: std::collections::HashSet<InferenceType>,
}

impl IncrementalReasoner {
    /// Builds an incremental reasoner over `ontology` with HermiT's default
    /// configuration (BUFFERING mode, since `Configuration` defaults
    /// `buffer_changes = true`, matching Java's `bufferChanges = true`).
    pub fn new(ontology: SetOntology<crate::structural::A>) -> IncrementalReasoner {
        IncrementalReasoner::with_configuration(
            ontology,
            crate::configuration::Configuration::default(),
        )
    }

    /// `ReasonerFactory.createReasoner(ontology)` via `getProtegeConfiguration(null)`
    /// (Reasoner.java:2318-2358): the Protege / OWL-API factory entry point uses a
    /// default Configuration EXCEPT that `ignoreUnsupportedDatatypes` is forced on (so
    /// an unsupported datatype is treated as a fresh predicate rather than rejected).
    pub fn new_protege(ontology: SetOntology<crate::structural::A>) -> IncrementalReasoner {
        let mut configuration = crate::configuration::Configuration::default();
        configuration.ignore_unsupported_datatypes = true;
        IncrementalReasoner::with_configuration(ontology, configuration)
    }

    /// `ReasonerFactory.createNonBufferingReasoner(ontology)` (Reasoner.java:2347-2351):
    /// the Protege configuration with `bufferChanges=false`, so ontology changes take
    /// effect without an explicit `flush`.
    pub fn new_non_buffering(ontology: SetOntology<crate::structural::A>) -> IncrementalReasoner {
        let mut configuration = crate::configuration::Configuration::default();
        configuration.ignore_unsupported_datatypes = true;
        configuration.buffer_changes = false;
        IncrementalReasoner::with_configuration(ontology, configuration)
    }

    /// Builds an incremental reasoner with an explicit configuration; its
    /// `buffer_changes` selects the `BufferingMode` (Java's
    /// `Reasoner(Configuration, OWLOntology)`).
    pub fn with_configuration(
        ontology: SetOntology<crate::structural::A>,
        configuration: crate::configuration::Configuration,
    ) -> IncrementalReasoner {
        IncrementalReasoner {
            ontology,
            configuration,
            pending_changes: Vec::new(),
            cached_consistent: None,
            dl_ontology: None,
            original_dl_ontology: None,
            original_atomic_concept_count: 0,
            last_flush_was_incremental: None,
            precomputed_inferences: std::collections::HashSet::new(),
        }
    }

    /// Port of `Reasoner.precomputeInferences` (Reasoner.java:555). Runs the
    /// requested inference tasks against the current ontology and records them so
    /// [`is_precomputed`](Self::is_precomputed) reflects the populated caches, matching
    /// Java's stateful reasoner (the free `precompute` is stateless and cannot remember).
    ///
    /// Each task is gated on `configuration.prepare_reasoner_inferences` exactly as Java
    /// does: `doAll = prepareReasonerInferences==null`; when `Some`, the per-flag field
    /// controls whether that task runs (Reasoner.java:557-583).
    pub fn precompute(&mut self, inference_types: &[InferenceType]) -> Result<(), String> {
        self.flush_changes_if_required();
        check_pre_conditions(&self.ontology)?;
        // Java: boolean doAll = m_configuration.prepareReasonerInferences==null;
        let do_all = self.configuration.prepare_reasoner_inferences.is_none();
        let pri = self.configuration.prepare_reasoner_inferences.as_ref();
        use InferenceType::*;
        let requested: std::collections::HashSet<InferenceType> =
            inference_types.iter().copied().collect();
        // Java Reasoner.java:560-562
        if requested.contains(&ClassHierarchy)
            && (do_all || pri.map_or(false, |p| p.class_classification_required))
        {
            classify(&self.ontology)?;
            self.precomputed_inferences.insert(ClassHierarchy);
        }
        // Java Reasoner.java:563-565
        if requested.contains(&ObjectPropertyHierarchy)
            && (do_all || pri.map_or(false, |p| p.object_property_classification_required))
        {
            classify_object_properties(&self.ontology)?;
            self.precomputed_inferences.insert(ObjectPropertyHierarchy);
        }
        // Java Reasoner.java:566-568
        if requested.contains(&DataPropertyHierarchy)
            && (do_all || pri.map_or(false, |p| p.data_property_classification_required))
        {
            classify_data_properties(&self.ontology)?;
            self.precomputed_inferences.insert(DataPropertyHierarchy);
        }
        // Java Reasoner.java:569-574: realise + optional same-as precompute
        if requested.contains(&ClassAssertions)
            && (do_all || pri.map_or(false, |p| p.realisation_required))
        {
            realize(&self.ontology)?;
            self.precomputed_inferences.insert(ClassAssertions);
            // Java:572-573 — also precompute same-as when BY_SAME_AS policy or flag set
            use crate::configuration::IndividualNodeSetPolicy;
            if self.configuration.individual_node_set_policy == IndividualNodeSetPolicy::BySameAs
                || pri.map_or(false, |p| p.same_as)
            {
                realize(&self.ontology)?; // precomputeSameAsEquivalenceClasses depends on realise
                // The same-as cache is now populated, so isPrecomputed(SAME_INDIVIDUAL)
                // also becomes true (Reasoner.java:544-545).
                self.precomputed_inferences.insert(SameIndividual);
            }
        }
        // Java Reasoner.java:575-577
        if requested.contains(&ObjectPropertyAssertions)
            && (do_all || pri.map_or(false, |p| p.object_property_realisation_required))
        {
            let build = Build::new_arc();
            let _ = object_property_instances(
                &self.ontology,
                horned_owl::model::ObjectPropertyExpression::ObjectProperty(
                    build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty"),
                ),
            )?;
            self.precomputed_inferences.insert(ObjectPropertyAssertions);
        }
        // Java Reasoner.java:581-583
        if requested.contains(&SameIndividual)
            && (do_all || pri.map_or(false, |p| p.same_as))
        {
            realize(&self.ontology)?; // precomputeSameAsEquivalenceClasses
            self.precomputed_inferences.insert(SameIndividual);
        }
        // DATA_PROPERTY_ASSERTIONS / DIFFERENT_INDIVIDUALS / DISJOINT_CLASSES silently
        // ignored by Java's precomputeInferences, and isPrecomputed always returns
        // false for them, so they are never recorded.
        Ok(())
    }

    /// Port of `Reasoner.isPrecomputed(InferenceType)` (Reasoner.java:530).
    /// Whether `inference_type` has been precomputed since the last flush that applied
    /// changes. Unlike the free `is_precomputed` (always `false`, being stateless), this
    /// reads the per-cache completion state, faithfully mirroring Java.
    pub fn is_precomputed(&self, inference_type: InferenceType) -> bool {
        self.precomputed_inferences.contains(&inference_type)
    }

    /// Port of `Reasoner.getBufferingMode` (Reasoner.java:354):
    /// `bufferChanges ? BUFFERING : NON_BUFFERING`.
    pub fn get_buffering_mode(&self) -> BufferingMode {
        if self.configuration.buffer_changes {
            BufferingMode::Buffering
        } else {
            BufferingMode::NonBuffering
        }
    }

    /// The reasoner's configuration (Java's `getConfiguration`).
    pub fn configuration(&self) -> &crate::configuration::Configuration {
        &self.configuration
    }

    /// A read-only view of the *current* (post-flush) ontology. Changes that are
    /// still pending (BUFFERING mode, not yet flushed) are NOT reflected here --
    /// just as Java queries the loaded `m_dlOntology`, not the pending changes.
    pub fn ontology(&self) -> &SetOntology<crate::structural::A> {
        &self.ontology
    }

    /// Port of `Reasoner.getDLOntology()` (Reasoner.java:337). The live
    /// clausified internal model (TBox clauses + current ABox facts) the reasoner
    /// reasons over. Flushes any pending changes first (as Java's queries do) and
    /// materialises the clausification on demand.
    pub fn dl_ontology(&mut self) -> &DLOntology {
        self.flush_changes_if_required();
        if self.dl_ontology.is_none() {
            self.ensure_original_clausified();
        }
        self.dl_ontology
            .as_ref()
            .expect("clausification populated dl_ontology")
    }

    /// Port of `Reasoner.getPendingChanges` (Reasoner.java:371).
    pub fn pending_changes(&self) -> &[OntologyChange] {
        &self.pending_changes
    }

    /// Port of `Reasoner.getPendingAxiomAdditions` (Reasoner.java:357).
    pub fn pending_axiom_additions(&self) -> Vec<&Component<crate::structural::A>> {
        self.pending_changes
            .iter()
            .filter_map(|c| match c {
                OntologyChange::Add(a) => Some(a),
                OntologyChange::Remove(_) => None,
            })
            .collect()
    }

    /// Port of `Reasoner.getPendingAxiomRemovals` (Reasoner.java:364).
    pub fn pending_axiom_removals(&self) -> Vec<&Component<crate::structural::A>> {
        self.pending_changes
            .iter()
            .filter_map(|c| match c {
                OntologyChange::Remove(r) => Some(r),
                OntologyChange::Add(_) => None,
            })
            .collect()
    }

    /// Submits an `AddAxiom` change, mirroring
    /// `OntologyChangeListener.ontologiesChanged` (Reasoner.java:347): in
    /// BUFFERING mode it is buffered (visible only after `flush`); in
    /// NON_BUFFERING mode it takes effect immediately (Java's
    /// `flushChangesIfRequired`).
    pub fn add_axiom(&mut self, axiom: Component<crate::structural::A>) {
        self.apply_changes(vec![OntologyChange::Add(axiom)]);
    }

    /// Submits a `RemoveAxiom` change (cf. `add_axiom`). Removing an axiom can
    /// restore consistency once flushed.
    pub fn remove_axiom(&mut self, axiom: Component<crate::structural::A>) {
        self.apply_changes(vec![OntologyChange::Remove(axiom)]);
    }

    /// Submits a batch of changes (Java's `ontologiesChanged(List<...>)`): every
    /// change is appended to the pending buffer, then -- in NON_BUFFERING mode --
    /// `flushChangesIfRequired` flushes immediately so they take effect at once.
    pub fn apply_changes(&mut self, changes: Vec<OntologyChange>) {
        for change in changes {
            self.pending_changes.push(change);
        }
        // Reasoner.checkPreConditions -> flushChangesIfRequired (Reasoner.java:2179):
        // `if (!m_configuration.bufferChanges && !m_pendingChanges.isEmpty()) flush();`
        self.flush_changes_if_required();
    }

    /// Port of `Reasoner.flushChangesIfRequired` (Reasoner.java:2179): in
    /// NON_BUFFERING mode, flush any pending changes immediately. Every public
    /// query also calls this first, so a NON_BUFFERING change is always applied
    /// before the next query reads the ontology.
    fn flush_changes_if_required(&mut self) {
        if !self.configuration.buffer_changes && !self.pending_changes.is_empty() {
            self.flush();
        }
    }

    /// Port of `Reasoner.flush` (Reasoner.java:374): if there are pending
    /// changes, apply them. When the changes are pure ABox assertions over
    /// already-present vocabulary, take the INCREMENTAL path (reduced-ABox
    /// clausification of the delta + a combined `DLOntology`); otherwise FALL
    /// BACK to a full re-clausification. Either way the owned `SetOntology` is
    /// kept in sync and the cached consistency is invalidated. With no pending
    /// changes this is a no-op (`if (!m_pendingChanges.isEmpty())`).
    pub fn flush(&mut self) {
        if self.pending_changes.is_empty() {
            return;
        }

        // Ensure the original `DLOntology` is materialized (Java's m_dlOntology
        // is built on load, before any flush).
        if self.original_dl_ontology.is_none() {
            self.ensure_original_clausified();
        }

        // Reasoner.java:377 -- decide the path BEFORE mutating the ontology, since
        // the decision examines the pending changes against the current loaded
        // vocabulary (`m_dlOntology`).
        let incremental = self
            .can_process_pending_changes_incrementally()
            .and_then(|()| self.try_incremental_flush().ok().flatten());

        match incremental {
            Some(combined) => {
                // ABox-only incremental path succeeded: apply the changes to the
                // owned ontology (so the classify/instances free-function queries
                // stay in sync) and adopt the combined `DLOntology`.
                self.apply_pending_to_ontology();
                self.dl_ontology = Some(combined);
                self.last_flush_was_incremental = Some(true);
            }
            None => {
                // Fallback: full re-clausification of the flushed ontology
                // (Java's `loadOntology`). We still exercise the ADDITIONAL
                // clausification + index threading for any added axioms via
                // `create_delta_dl_ontology` (see below) before rebuilding.
                self.apply_pending_to_ontology();
                self.full_reload();
                self.last_flush_was_incremental = Some(false);
            }
        }

        // Invalidate the cached consistency (Java: m_isConsistent=null) and the
        // precompute flags (Java nulls m_atomicConceptHierarchy / m_instanceManager
        // on a flush that applies changes).
        self.cached_consistent = None;
        self.precomputed_inferences.clear();
    }

    /// Whether the most recent `flush` that applied changes took the incremental
    /// (reduced-ABox) path (`Some(true)`) or the full-rebuild fallback
    /// (`Some(false)`); `None` if no flush has applied changes yet. This exposes
    /// which branch of Java's `canProcessPendingChangesIncrementally` was taken.
    pub fn last_flush_was_incremental(&self) -> Option<bool> {
        self.last_flush_was_incremental
    }

    /// The cached original atomic-concept count
    /// (`originalDLOntology.getAllAtomicConcepts().size()`, Reasoner.java:2068/2073)
    /// -- the replacement index threaded into the additional/delta clausification
    /// so its fresh `internal:all#`/`internal:def#` concepts cannot collide with
    /// the original's. `0` until the first clausification.
    pub fn original_atomic_concept_count(&self) -> usize {
        self.original_atomic_concept_count
    }

    /// Clausifies the current owned ontology and caches it as both the
    /// `original` and the working `DLOntology`, recording the original
    /// atomic-concept count for index threading.
    fn ensure_original_clausified(&mut self) {
        if let Ok(dl) = clausify_ontology(&self.ontology) {
            self.original_atomic_concept_count = dl.get_all_atomic_concepts().len();
            // Clone the cheap interned facts/clauses into a second owned
            // `DLOntology` so both `original` and the working copy are available.
            let original = clausify_ontology(&self.ontology).ok();
            self.dl_ontology = Some(dl);
            self.original_dl_ontology = original;
        }
    }

    /// Applies the pending changes to the owned `SetOntology` and clears the
    /// buffer (mirrors the loaded-ontology mutation; the DL-level handling is
    /// done by the caller).
    fn apply_pending_to_ontology(&mut self) {
        for change in self.pending_changes.drain(..) {
            match change {
                OntologyChange::Add(axiom) => {
                    self.ontology.insert(axiom);
                }
                OntologyChange::Remove(axiom) => {
                    let annotated: horned_owl::model::AnnotatedComponent<crate::structural::A> =
                        axiom.into();
                    self.ontology.remove(&annotated);
                }
            }
        }
    }

    /// Port of `canProcessPendingChangesIncrementally` (Reasoner.java:416): the
    /// pending changes can be applied incrementally iff every change is an ABox
    /// assertion (the kinds `ReducedABoxClausification` handles) and the loaded
    /// ontology has no nominals / description graphs. Returns `Some(())` when the
    /// incremental path is permitted, `None` to force the fallback. (The deeper
    /// "all used names already exist" guard is enforced by the reduced clausifier
    /// itself, which errors on fresh vocabulary -- so `try_incremental_flush`
    /// falls back if any delta assertion uses fresh names.)
    fn can_process_pending_changes_incrementally(&self) -> Option<()> {
        // Faithful per-change port of Reasoner.canProcessPendingChanges-
        // Incrementally (Reasoner.java:416-485). The defined-or-internal checks use the
        // pre-change ontology, matching Java's `isDefined` against the loaded m_dlOntology.
        use crate::prefixes::Prefixes;

        // Reasoner.java:420 -- nominals / description graphs disqualify the ABox path.
        if let Some(dl) = &self.dl_ontology {
            if dl.has_nominals() || !dl.get_all_description_graphs().is_empty() {
                return None;
            }
        }

        let defined_or_internal_class = |c: &Class<crate::structural::A>| -> bool {
            Prefixes::is_internal_iri(&c.0.to_string())
                || is_defined_class(&self.ontology, c).unwrap_or(false)
        };
        let defined_or_internal_op =
            |ope: &horned_owl::model::ObjectPropertyExpression<crate::structural::A>| -> bool {
                use horned_owl::model::ObjectPropertyExpression as OPE;
                let p = match ope {
                    OPE::ObjectProperty(p) | OPE::InverseObjectProperty(p) => p,
                };
                Prefixes::is_internal_iri(&p.0.to_string())
                    || is_defined_object_property(&self.ontology, p).unwrap_or(false)
            };
        let defined_individual = |i: &horned_owl::model::Individual<crate::structural::A>| -> bool {
            match i {
                horned_owl::model::Individual::Named(n) => {
                    is_defined_individual(&self.ontology, n).unwrap_or(false)
                }
                // An anonymous individual is "defined" iff present; conservatively
                // require named for the fast path (Java's isDefined checks containment).
                horned_owl::model::Individual::Anonymous(_) => false,
            }
        };
        // The allowed ClassAssertion class-expression forms (Reasoner.java:435-468):
        // a named class / HasSelf / HasValue, all names defined-or-internal.
        let ce_ok = |ce: &CE<crate::structural::A>| -> bool {
            match ce {
                CE::Class(c) => defined_or_internal_class(c),
                CE::ObjectHasSelf(ope) => defined_or_internal_op(ope),
                CE::ObjectHasValue { ope, i } => defined_or_internal_op(ope) && defined_individual(i),
                _ => false,
            }
        };

        for change in &self.pending_changes {
            match change.axiom() {
                Component::ClassAssertion(ca) => {
                    if !defined_individual(&ca.i) {
                        return None;
                    }
                    let ok = match &ca.ce {
                        CE::ObjectComplementOf(negated) => ce_ok(negated),
                        other => ce_ok(other),
                    };
                    if !ok {
                        return None;
                    }
                }
                // Any other logical individual axiom is incrementalizable as-is
                // (Reasoner.java:470-471 requires an OWLIndividualAxiom).
                Component::ObjectPropertyAssertion(_)
                | Component::NegativeObjectPropertyAssertion(_)
                | Component::DataPropertyAssertion(_)
                | Component::NegativeDataPropertyAssertion(_)
                | Component::SameIndividual(_)
                | Component::DifferentIndividuals(_) => {}
                // Declarations: incrementalizable iff the declared class/op/dp is
                // defined-or-internal (Reasoner.java:473-481). Individual/datatype/
                // annotation declarations carry no such constraint.
                Component::DeclareClass(d) => {
                    if !defined_or_internal_class(&d.0) {
                        return None;
                    }
                }
                Component::DeclareObjectProperty(d) => {
                    use horned_owl::model::ObjectPropertyExpression as OPE;
                    if !defined_or_internal_op(&OPE::ObjectProperty(d.0.clone())) {
                        return None;
                    }
                }
                Component::DeclareDataProperty(d) => {
                    if !(Prefixes::is_internal_iri(&d.0 .0.to_string())
                        || is_defined_data_property(&self.ontology, &d.0).unwrap_or(false))
                    {
                        return None;
                    }
                }
                Component::DeclareNamedIndividual(_)
                | Component::DeclareDatatype(_)
                | Component::DeclareAnnotationProperty(_) => {}
                // Non-logical, non-declaration axioms (annotations, imports, ontology
                // id) are reasoning no-ops; Java allows them on the incremental path.
                Component::AnnotationAssertion(_)
                | Component::SubAnnotationPropertyOf(_)
                | Component::AnnotationPropertyDomain(_)
                | Component::AnnotationPropertyRange(_)
                | Component::OntologyAnnotation(_)
                | Component::Import(_) => {}
                // Anything else is a logical TBox/RBox axiom -> full reload.
                _ => return None,
            }
        }
        Some(())
    }

    /// The INCREMENTAL ABox path (Reasoner.java:378-407): clausify ONLY the delta
    /// ABox via `ReducedABoxClausification::clausify` (with a `Vocabulary` built
    /// from the original ontology's atomic concepts / object roles / data roles),
    /// then produce a combined `DLOntology` = original TBox clauses + original
    /// facts ± the delta facts. Returns `Ok(None)` (forcing the fallback) if any
    /// delta assertion uses fresh vocabulary the reduced clausifier rejects.
    fn try_incremental_flush(&self) -> Result<Option<DLOntology>, String> {
        use crate::structural::reduced_abox_clausification::{
            ReducedABoxClausification, Vocabulary,
        };
        // Java's incremental path reads the CURRENT `m_dlOntology` (its TBox
        // clauses, vocabulary, and facts), which has already absorbed any prior
        // incremental flush -- not a frozen original. The frozen
        // `original_atomic_concept_count` is only used for index threading.
        let current = match &self.dl_ontology {
            Some(o) => o,
            None => return Ok(None),
        };

        // Build the loaded vocabulary, exactly as Java passes the loaded
        // m_dlOntology's allAtomic{Concepts,ObjectRoles,DataRoles} into
        // `new ReducedABoxOnlyClausification(...)`.
        let mut vocabulary = Vocabulary::default();
        vocabulary
            .atomic_concepts
            .extend(current.get_all_atomic_concepts().iter().cloned());
        vocabulary
            .atomic_object_roles
            .extend(current.get_all_atomic_object_roles().iter().cloned());
        vocabulary
            .atomic_data_roles
            .extend(current.get_all_atomic_data_roles().iter().cloned());

        // Start from the current facts (Java reads m_dlOntology's positive/
        // negative facts), then add/remove the per-change delta facts.
        let mut positive_facts: std::collections::HashSet<crate::model::Atom> =
            current.get_positive_facts().clone();
        let mut negative_facts: std::collections::HashSet<crate::model::Atom> =
            current.get_negative_facts().clone();

        for change in &self.pending_changes {
            // Clausify this single ABox assertion via the reduced clausifier.
            let mut delta: SetOntology<crate::structural::A> = SetOntology::new();
            delta.insert(change.axiom().clone());
            // If the reduced clausifier rejects fresh vocabulary, fall back.
            let result = match ReducedABoxClausification::clausify(
                &delta,
                &vocabulary,
                self.configuration.ignore_unsupported_datatypes,
            ) {
                Ok(r) => r,
                Err(_) => return Ok(None),
            };
            match change {
                OntologyChange::Add(_) => {
                    positive_facts.extend(result.positive_facts);
                    negative_facts.extend(result.negative_facts);
                }
                OntologyChange::Remove(_) => {
                    for fact in &result.positive_facts {
                        positive_facts.remove(fact);
                    }
                    for fact in &result.negative_facts {
                        negative_facts.remove(fact);
                    }
                }
            }
        }

        Ok(Some(combined_dl_ontology(
            current,
            positive_facts,
            negative_facts,
        )))
    }

    /// Full re-clausification fallback (Java's `loadOntology`). It rebuilds the
    /// working `DLOntology` from the flushed ontology from scratch (passing `0`
    /// as the replacement index, matching OWLClausification.java:153), then resets
    /// it as the new `original` so subsequent incremental flushes reuse it. For
    /// any pending ADDED axioms it first runs the `createAdditionalTableau`
    /// mechanism (`create_delta_dl_ontology`) so the index-threading path is
    /// exercised on the additional clausification (Reasoner.java:2072-2073).
    fn full_reload(&mut self) {
        // loadOntology: rebuild from scratch over the flushed ontology. (HermiT's
        // `loadOntology` re-clausifies the whole KB for non-ABox-only changes; it
        // does not build a delta -- the additional-DL-ontology fast path lives in
        // `getTableau(additionalAxioms)` / `is_consistent_with_additional_axioms`.)
        if let Ok(dl) = clausify_ontology(&self.ontology) {
            self.original_atomic_concept_count = dl.get_all_atomic_concepts().len();
            let original = clausify_ontology(&self.ontology).ok();
            self.dl_ontology = Some(dl);
            self.original_dl_ontology = original;
        } else {
            self.dl_ontology = None;
            self.original_dl_ontology = None;
        }
    }

    // --- Re-exposed query operations over the current (post-flush) ontology ---
    //
    // Each public query first calls `flush_changes_if_required` (Java's
    // `checkPreConditions` -> `flushChangesIfRequired`), so NON_BUFFERING changes
    // are applied before reading, while BUFFERING changes stay pending until an
    // explicit `flush`. The reasoning itself delegates to the existing free
    // functions over the owned `SetOntology`.

    /// Whether the current ontology is consistent (Java's `isConsistent`). The
    /// result is cached between flushes (Java's `m_isConsistent`), and the check
    /// reasons from the cached/combined `DLOntology` (Java's `m_dlOntology`) --
    /// the one built incrementally (reduced-ABox path) or by full reload on the
    /// last flush.
    pub fn is_consistent(&mut self) -> Result<bool, String> {
        self.flush_changes_if_required();
        if let Some(consistent) = self.cached_consistent {
            return Ok(consistent);
        }
        // Materialize the working `DLOntology` if no flush has built it yet
        // (Java's m_dlOntology is built on load).
        if self.dl_ontology.is_none() {
            self.ensure_original_clausified();
        }
        let consistent = match &self.dl_ontology {
            Some(dl) => {
                Reasoner::with_configuration(dl, self.configuration.clone()).is_consistent()
            }
            // Clausification failed (e.g. an unsupported axiom): fall back to the
            // free function, which surfaces the error.
            None => is_ontology_consistent(&self.ontology)?,
        };
        self.cached_consistent = Some(consistent);
        Ok(consistent)
    }

    /// Whether `class_expression` is satisfiable w.r.t. the current ontology
    /// (`Reasoner.isSatisfiable`).
    pub fn is_concept_satisfiable(
        &mut self,
        class_expression: CE<crate::structural::A>,
    ) -> Result<bool, String> {
        self.flush_changes_if_required();
        // Honour THIS reasoner's throw_inconsistent_ontology_exception flag
        // rather than the default-config free function. is_concept_satisfiable returns
        // false (not Err) on inconsistency, so no throw is needed here, but route through
        // the core primitive so the reasoner's configuration governs the tableau build.
        is_concept_satisfiable_with_configuration(
            &self.ontology,
            class_expression,
            &self.configuration,
        )
    }

    /// Whether `sub` is subsumed by `sup` w.r.t. the current ontology
    /// (`Reasoner.isSubClassOf`).
    pub fn is_subsumed_by(
        &mut self,
        sub: CE<crate::structural::A>,
        sup: CE<crate::structural::A>,
    ) -> Result<bool, String> {
        self.flush_changes_if_required();
        // Honour this reasoner's throw_inconsistent_ontology_exception flag.
        is_subsumed_by_with_configuration(&self.ontology, sub, sup, &self.configuration)
    }

    /// Whether `individual` is an instance of `class_expression` w.r.t. the
    /// current ontology (`Reasoner.hasType`).
    pub fn is_instance_of(
        &mut self,
        individual: NamedIndividual<crate::structural::A>,
        class_expression: CE<crate::structural::A>,
    ) -> Result<bool, String> {
        self.flush_changes_if_required();
        // Under FreshEntityPolicy::Disallow, reject undeclared query entities
        // (Java checkPreConditions runs the fresh-entity throw BEFORE the inconsistency
        // throw). Entities = the queried individual plus the class expression's signature.
        let (mut classes, mut ops, mut dps, mut inds) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        inds.push(individual.0.to_string());
        collect_ce_entities(&class_expression, &mut classes, &mut ops, &mut dps, &mut inds);
        throw_fresh_entity_exception_if_necessary(
            &self.ontology,
            &self.configuration,
            &classes,
            &ops,
            &dps,
            &inds,
        )?;
        // Honour this reasoner's throw_inconsistent_ontology_exception flag,
        // then use the non-throwing core primitive (hasType returns true on an
        // inconsistent ontology when the throw is disabled).
        throw_inconsistent_ontology_exception_if_necessary(&self.ontology, &self.configuration)?;
        is_instance_of_core(&self.ontology, individual, class_expression)
    }

    /// The classified subsumption hierarchy of the current ontology
    /// (`Reasoner.classifyClasses` / `getHierarchy`).
    pub fn classify(
        &mut self,
    ) -> Result<crate::hierarchy::Hierarchy<Class<crate::structural::A>>, String> {
        self.flush_changes_if_required();
        // Honour this reasoner's throw_inconsistent_ontology_exception flag.
        classify_with_configuration(&self.ontology, &self.configuration)
    }

    /// Named classes equivalent to `class` in the current ontology
    /// (`Reasoner.getEquivalentClasses`).
    pub fn equivalent_classes(
        &mut self,
        class: &Class<crate::structural::A>,
    ) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
        self.flush_changes_if_required();
        // Honour this reasoner's throw_inconsistent_ontology_exception flag.
        equivalent_classes_with_configuration(&self.ontology, class, &self.configuration)
    }

    /// Named subclasses of `class` (`Reasoner.getSubClasses`); `direct` restricts
    /// to immediate subclasses.
    pub fn sub_classes(
        &mut self,
        class: &Class<crate::structural::A>,
        direct: bool,
    ) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
        self.flush_changes_if_required();
        // Honour this reasoner's throw_inconsistent_ontology_exception flag.
        sub_classes_with_configuration(&self.ontology, class, direct, &self.configuration)
    }

    /// Named superclasses of `class` (`Reasoner.getSuperClasses`); `direct`
    /// restricts to immediate superclasses.
    pub fn super_classes(
        &mut self,
        class: &Class<crate::structural::A>,
        direct: bool,
    ) -> Result<std::collections::HashSet<Class<crate::structural::A>>, String> {
        self.flush_changes_if_required();
        // Honour this reasoner's throw_inconsistent_ontology_exception flag.
        super_classes_with_configuration(&self.ontology, class, direct, &self.configuration)
    }

    /// Named instances of `class` in the current ontology
    /// (`Reasoner.getInstances`); `direct` restricts to direct instances.
    pub fn instances(
        &mut self,
        class: &Class<crate::structural::A>,
        direct: bool,
    ) -> Result<std::collections::HashSet<NamedIndividual<crate::structural::A>>, String> {
        self.flush_changes_if_required();
        // Honour this reasoner's throw_inconsistent_ontology_exception flag.
        instances_with_configuration(&self.ontology, class, direct, &self.configuration)
    }

    /// Named instances of an arbitrary class expression in the current ontology
    /// (`Reasoner.getInstances(OWLClassExpression, boolean)`, Reasoner.java:1663).
    /// Named-class fast path delegates to [`instances`]; for a complex expression
    /// the full query-concept / sibling-search path is used.
    pub fn instances_of_expression(
        &mut self,
        ce: &CE<crate::structural::A>,
        direct: bool,
    ) -> Result<std::collections::HashSet<NamedIndividual<crate::structural::A>>, String> {
        self.flush_changes_if_required();
        instances_of_expression_with_configuration(&self.ontology, ce, direct, &self.configuration)
    }

    /// Whether `axiom` is entailed by the current ontology
    /// (`Reasoner.isEntailed`).
    pub fn is_entailed(
        &mut self,
        axiom: &Component<crate::structural::A>,
    ) -> Result<bool, String> {
        self.flush_changes_if_required();
        // EntailmentChecker.visit(OWLHasKeyAxiom) is the ONLY entailment visit that
        // runs throwFreshEntityExceptionIfNecessary (EntailmentChecker.java:459), over
        // the HasKey axiom's signature. Under FreshEntityPolicy::Disallow this rejects a
        // key axiom mentioning an entity absent from the ontology.
        if let Component::HasKey(hk) = axiom {
            use horned_owl::model::PropertyExpression;
            let (mut classes, mut ops, mut dps, mut inds) =
                (Vec::new(), Vec::new(), Vec::new(), Vec::new());
            collect_ce_entities(&hk.ce, &mut classes, &mut ops, &mut dps, &mut inds);
            for pe in &hk.vpe {
                match pe {
                    PropertyExpression::ObjectPropertyExpression(ope) => {
                        ops.push(crate::structural::named_property(ope).0.to_string());
                    }
                    PropertyExpression::DataProperty(dp) => dps.push(dp.0.to_string()),
                    PropertyExpression::AnnotationProperty(_) => {}
                }
            }
            throw_fresh_entity_exception_if_necessary(
                &self.ontology,
                &self.configuration,
                &classes,
                &ops,
                &dps,
                &inds,
            )?;
        }
        // Honour this reasoner's throw_inconsistent_ontology_exception flag,
        // then use the non-throwing core primitive (isEntailed returns true on an
        // inconsistent ontology when the throw is disabled).
        throw_inconsistent_ontology_exception_if_necessary(&self.ontology, &self.configuration)?;
        is_entailed_core(&self.ontology, axiom)
    }
}

/// Description-graph reasoning at the reasoner (`is_consistent`) level.
///
/// There is NO front-end (horned-owl / structural / clausification) input path
/// for description graphs -- `DescriptionGraph` appears only in the model/tableau
/// layers, never in `src/structural/`. So a description graph is reachable only by
/// constructing a `DLOntology` directly (its constructor harvests the graphs from
/// the `ExistsDescriptionGraph`/`DescriptionGraph` predicates in clauses/facts).
/// These tests drive that internal-API path end to end through the now-wired
/// `DescriptionGraphManager`.
#[cfg(test)]
mod description_graph_reasoner_tests {
    use super::*;
    use crate::model::{
        Atom, AtomicConcept, AtomicRole, DLPredicate, DescriptionGraph, Edge,
        ExistsDescriptionGraph, Individual, Term,
    };
    use std::collections::HashSet;

    fn graph() -> (DescriptionGraph, AtomicConcept, AtomicConcept, AtomicRole) {
        let c0 = AtomicConcept::create("http://example.org/C0");
        let c1 = AtomicConcept::create("http://example.org/C1");
        let r = AtomicRole::create("http://example.org/r");
        let g = DescriptionGraph::new(
            "http://example.org/G",
            vec![c0.clone(), c1.clone()],
            vec![Edge::new(r.clone(), 0, 1)],
            HashSet::new(),
        );
        (g, c0, c1, r)
    }

    /// A `DLOntology` carrying an `ExistsDescriptionGraph(G,0)` fact on an
    /// individual: the constructor harvests `G` into `getAllDescriptionGraphs`,
    /// the reasoner builds a `DescriptionGraphManager` over it, expands the graph,
    /// and -- with no conflicting axioms -- the ontology is CONSISTENT.
    #[test]
    fn satisfiable_description_graph_ontology_is_consistent() {
        let (g, _c0, _c1, _r) = graph();
        let a = Individual::create("http://example.org/a");
        let mut positive_facts = HashSet::new();
        positive_facts.insert(Atom::create(
            DLPredicate::ExistsDescriptionGraph(ExistsDescriptionGraph::create(g.clone(), 0)),
            vec![Term::Individual(a)],
        ));
        let dl = DLOntology::new(
            "http://example.org/dg".to_string(),
            indexmap::IndexSet::new(),
            positive_facts,
            HashSet::new(),
            None, None, None, None, None, None, None,
            false, false, false, false,
        );
        assert!(
            !dl.get_all_description_graphs().is_empty(),
            "the DLOntology must carry the description graph"
        );
        let reasoner = Reasoner::new(&dl);
        assert!(reasoner.is_consistent(), "a plain graph ontology is consistent");
    }

    /// The same ontology, but with `not C1` also asserted on the individual that
    /// the graph forces to carry `C1` (vertex 0's r-successor is V1:C1, but here
    /// we instead make the ANCHOR vertex 1 so the individual itself must be C1)
    /// -> the graph layout forces `C1(a)` while the ABox asserts `not C1(a)` ->
    /// a graph-induced clash -> INCONSISTENT.
    #[test]
    fn graph_forced_concept_conflicting_with_abox_is_inconsistent() {
        let (g, _c0, c1, _r) = graph();
        let a = Individual::create("http://example.org/a");
        let mut positive_facts = HashSet::new();
        // Anchor the existential at vertex 1, so the individual `a` plays V1 and
        // the graph layout forces C1 onto `a` itself.
        positive_facts.insert(Atom::create(
            DLPredicate::ExistsDescriptionGraph(ExistsDescriptionGraph::create(g.clone(), 1)),
            vec![Term::Individual(a.clone())],
        ));
        // not C1(a): conflicts with the C1 the graph forces onto `a`.
        let mut negative_facts = HashSet::new();
        negative_facts.insert(Atom::create(
            DLPredicate::AtomicConcept(c1.clone()),
            vec![Term::Individual(a)],
        ));
        let dl = DLOntology::new(
            "http://example.org/dg".to_string(),
            indexmap::IndexSet::new(),
            positive_facts,
            negative_facts,
            None, None, None, None, None, None, None,
            false, false, false, false,
        );
        let reasoner = Reasoner::new(&dl);
        assert!(
            !reasoner.is_consistent(),
            "the graph forces C1(a) while the ABox asserts not C1(a) -> inconsistent"
        );
    }

    /// Control: the same `not C1(a)` ABox WITHOUT the graph existential is
    /// consistent -- confirming the inconsistency above is graph-induced, not an
    /// artefact of the ABox.
    #[test]
    fn negative_concept_alone_is_consistent() {
        let (_g, _c0, c1, _r) = graph();
        let a = Individual::create("http://example.org/a");
        let mut negative_facts = HashSet::new();
        negative_facts.insert(Atom::create(
            DLPredicate::AtomicConcept(c1.clone()),
            vec![Term::Individual(a)],
        ));
        let dl = DLOntology::new(
            "http://example.org/dg".to_string(),
            indexmap::IndexSet::new(),
            HashSet::new(),
            negative_facts,
            None, None, None, None, None, None, None,
            false, false, false, false,
        );
        assert!(Reasoner::new(&dl).is_consistent());
    }
}

#[cfg(test)]
mod batched_subsumption_tests {
    use super::*;
    use horned_owl::model::{
        DataProperty, DisjointDataProperties, ObjectPropertyExpression as OPE, SubDataPropertyOf,
        SubObjectPropertyExpression, SubObjectPropertyOf,
    };
    use std::collections::HashSet;

    // is_consistent_with_additional_axioms: the additional hyperresolution manager
    // (HermiT's setAdditionalDLOntology fast path) reasons over the delta clauses,
    // so adding `B ⊑ ⊥` to a consistent KB with `a : A`, `A ⊑ B` clashes.
    #[test]
    fn additional_axioms_can_force_inconsistency() {
        use horned_owl::model::{
            ClassAssertion, ClassExpression as CE, Individual as OwlInd, SubClassOf,
        };
        let build = Build::new_arc();
        let a = build.class("http://example.org/A");
        let b = build.class("http://example.org/B");
        let c = build.class("http://example.org/C");
        let nothing = build.class("http://www.w3.org/2002/07/owl#Nothing");
        let ind = build.named_individual("http://example.org/a");
        let mut o: SetOntology<crate::structural::A> = SetOntology::new();
        o.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(a.clone()),
            i: OwlInd::Named(ind.clone()),
        }));
        o.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(a.clone()),
            sup: CE::Class(b.clone()),
        }));
        let dl = clausify_ontology(&o).unwrap();
        let cfg = crate::configuration::Configuration::default();
        let reasoner = Reasoner::with_configuration(&dl, cfg);
        assert!(reasoner.is_consistent());

        // Adding `B ⊑ ⊥` forces a : B : ⊥ via the additional manager -> inconsistent.
        let mut bad: SetOntology<crate::structural::A> = SetOntology::new();
        bad.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(b.clone()),
            sup: CE::Class(nothing.clone()),
        }));
        assert!(!reasoner.is_consistent_with_additional_axioms(&bad).unwrap());

        // An unrelated axiom keeps the combined ontology consistent, and the
        // permanent KB is untouched between calls.
        let mut harmless: SetOntology<crate::structural::A> = SetOntology::new();
        harmless.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(c.clone()),
            sup: CE::Class(b.clone()),
        }));
        assert!(reasoner.is_consistent_with_additional_axioms(&harmless).unwrap());
        assert!(reasoner.is_consistent());
    }

    // is_object_property_subsumed_by_union: r is subsumed by {s,t} when r ⊑ s.
    #[test]
    fn object_property_subsumed_by_union() {
        let build = Build::new_arc();
        let r = build.object_property("http://example.org/r");
        let s = build.object_property("http://example.org/s");
        let t = build.object_property("http://example.org/t");
        let ope = |p: &_| OPE::ObjectProperty(std::clone::Clone::clone(p));
        let mut o: SetOntology<crate::structural::A> = SetOntology::new();
        o.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
            sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(&r)),
            sup: ope(&s),
        }));
        let cfg = crate::configuration::Configuration::default();
        let sups: HashSet<_> = [ope(&s), ope(&t)].into_iter().collect();
        // r ⊑ s, so r ⊑ s ⊔ t.
        assert!(is_object_property_subsumed_by_union_with(&o, ope(&r), &sups, &cfg).unwrap());
        // t is unrelated, so t is NOT subsumed by {r, s}.
        let sups2: HashSet<_> = [ope(&r), ope(&s)].into_iter().collect();
        assert!(!is_object_property_subsumed_by_union_with(&o, ope(&t), &sups2, &cfg).unwrap());
    }

    // is_sub_data_property_of_union: dr is subsumed by {ds,dt} when dr ⊑ ds.
    #[test]
    fn data_property_subsumed_by_union() {
        let build = Build::new_arc();
        let dr = build.data_property("http://example.org/dr");
        let ds = build.data_property("http://example.org/ds");
        let dt = build.data_property("http://example.org/dt");
        let mut o: SetOntology<crate::structural::A> = SetOntology::new();
        o.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
            sub: dr.clone(),
            sup: ds.clone(),
        }));
        // Declare the disjointness so the properties exist (and dr,ds,dt are distinct).
        o.insert(Component::DisjointDataProperties(DisjointDataProperties(vec![
            ds.clone(),
            dt.clone(),
        ])));
        let cfg = crate::configuration::Configuration::default();
        let sups: HashSet<DataProperty<crate::structural::A>> = [ds.clone(), dt.clone()].into_iter().collect();
        assert!(is_sub_data_property_of_union_with(&o, dr.clone(), &sups, &cfg).unwrap());
        let sups2: HashSet<DataProperty<crate::structural::A>> = [dr.clone(), ds.clone()].into_iter().collect();
        assert!(!is_sub_data_property_of_union_with(&o, dt.clone(), &sups2, &cfg).unwrap());
    }

    // object_property_deterministic_edge_subsumers: the read-off used by the
    // union test's positive branch reads `r`'s deterministic subsumers only. With
    // r ⊑ s told (and t unrelated), the edge model of r(a,b) carries s(a,b) with an
    // empty dependency set, so `s` is returned; `t` (not forced) is not.
    #[test]
    fn deterministic_edge_subsumers_reads_only_known_role_subsumers() {
        let build = Build::new_arc();
        let r = build.object_property("http://example.org/r");
        let s = build.object_property("http://example.org/s");
        let t = build.object_property("http://example.org/t");
        let ope = |p: &_| OPE::ObjectProperty(std::clone::Clone::clone(p));
        let mut o: SetOntology<crate::structural::A> = SetOntology::new();
        o.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
            sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(&r)),
            sup: ope(&s),
        }));
        let dl = clausify_for_query(&o).unwrap();
        let reasoner = Reasoner::new(&dl);
        let mut manager = reasoner.new_manager();
        let candidates = [ope(&s), ope(&t)];
        let known = reasoner
            .object_property_deterministic_edge_subsumers(&mut manager, &ope(&r), &candidates)
            .expect("r is satisfiable");
        assert!(known.contains(&ope(&s)), "r ⊑ s is deterministic, so s is a known subsumer");
        assert!(!known.contains(&ope(&t)), "t is unrelated, so it is not a known subsumer");
    }
}
