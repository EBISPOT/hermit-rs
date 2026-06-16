// Tests for the incremental, mutable OWLReasoner (`IncrementalReasoner`).
//
// These exercise the faithful mapping of HermiT's `Reasoner` buffering/flush
// machinery (Reasoner.java): a buffered change is invisible until `flush()`, a
// non-buffered change takes effect immediately, removing an axiom restores
// consistency after flush, classification reflects a flushed `SubClassOf`, and
// `flush()` with no pending changes is a no-op.

use horned_owl::model::{
    Build, ClassAssertion, ClassExpression as CE, Component, DeclareClass, DeclareObjectProperty,
    DisjointClasses, Individual, MutableOntology, ObjectPropertyExpression as OPE, SubClassOf,
    TransitiveObjectProperty,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner::{BufferingMode, IncrementalReasoner, OntologyChange};
use hermit_rs::structural::A;

/// Base ontology: DisjointClasses(A, B) and A(a). Consistent on its own.
fn base_ontology() -> SetOntology<A> {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let ind_a = build.named_individual("http://example.org/a");

    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a),
        i: Individual::Named(ind_a),
    }));
    o
}

/// The B(a) assertion that, added to the base, contradicts DisjointClasses(A,B).
fn b_of_a() -> Component<A> {
    let build = Build::new_arc();
    let b = build.class("http://example.org/B");
    let ind_a = build.named_individual("http://example.org/a");
    Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(b),
        i: Individual::Named(ind_a),
    })
}

// (1) BUFFERING mode: a query AFTER add_axiom but BEFORE flush sees the OLD
// ontology; only after flush does it reflect the new one.
#[test]
fn buffered_add_not_visible_until_flush() {
    let mut reasoner = IncrementalReasoner::new(base_ontology());
    assert_eq!(reasoner.get_buffering_mode(), BufferingMode::Buffering);

    // Base is consistent.
    assert!(reasoner.is_consistent().unwrap());

    // Buffer B(a): the change is pending, so the ontology is still the old one.
    reasoner.add_axiom(b_of_a());
    assert_eq!(reasoner.pending_changes().len(), 1);
    assert!(
        reasoner.is_consistent().unwrap(),
        "buffered change must NOT be visible before flush"
    );

    // Flush: now B(a) is applied and the ontology becomes inconsistent.
    reasoner.flush();
    assert!(reasoner.pending_changes().is_empty());
    assert!(
        !reasoner.is_consistent().unwrap(),
        "after flush the added B(a) makes A/B disjointness contradicted"
    );
}

// (2) NON_BUFFERING mode: the add takes effect immediately, no flush needed.
#[test]
fn non_buffered_add_immediately_visible() {
    let mut config = hermit_rs::configuration::Configuration::default();
    config.buffer_changes = false;
    let mut reasoner = IncrementalReasoner::with_configuration(base_ontology(), config);
    assert_eq!(reasoner.get_buffering_mode(), BufferingMode::NonBuffering);

    assert!(reasoner.is_consistent().unwrap());

    // No explicit flush: the change applies on submission.
    reasoner.add_axiom(b_of_a());
    assert!(
        reasoner.pending_changes().is_empty(),
        "NON_BUFFERING flushes on submission"
    );
    assert!(
        !reasoner.is_consistent().unwrap(),
        "non-buffered change is visible immediately"
    );
}

// (4) Removing an axiom that makes an inconsistent ontology consistent again
// works after flush.
#[test]
fn remove_restores_consistency_after_flush() {
    // Start from base + B(a): inconsistent.
    let mut o = base_ontology();
    o.insert(b_of_a());
    let mut reasoner = IncrementalReasoner::new(o);
    assert!(!reasoner.is_consistent().unwrap());

    // Buffer removal of B(a): still inconsistent before flush.
    reasoner.remove_axiom(b_of_a());
    assert!(
        !reasoner.is_consistent().unwrap(),
        "buffered removal not visible before flush"
    );

    // Flush: B(a) gone, consistency restored.
    reasoner.flush();
    assert!(
        reasoner.is_consistent().unwrap(),
        "removing the contradicting B(a) restores consistency after flush"
    );
}

// Classification reflects a flushed SubClassOf(A, B).
#[test]
fn classification_reflects_flushed_subclassof() {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");

    // Two unrelated, satisfiable named classes (with declarations so they are in
    // the vocabulary).
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DeclareClass(horned_owl::model::DeclareClass(a.clone())));
    o.insert(Component::DeclareClass(horned_owl::model::DeclareClass(b.clone())));
    let mut reasoner = IncrementalReasoner::new(o);

    // Initially A is NOT a subclass of B.
    assert!(!reasoner
        .super_classes(&a, false)
        .unwrap()
        .contains(&b));

    // Buffer SubClassOf(A, B); not visible until flush.
    let sub = Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    });
    reasoner.add_axiom(sub);
    assert!(
        !reasoner.super_classes(&a, false).unwrap().contains(&b),
        "subclass edge not visible before flush"
    );

    // After flush, A ⊑ B is reflected in the classification.
    reasoner.flush();
    assert!(
        reasoner.super_classes(&a, false).unwrap().contains(&b),
        "classification must reflect the flushed SubClassOf(A,B)"
    );
    assert!(reasoner.sub_classes(&b, false).unwrap().contains(&a));
    assert!(reasoner
        .is_entailed(&Component::SubClassOf(SubClassOf {
            sub: CE::Class(a.clone()),
            sup: CE::Class(b.clone()),
        }))
        .unwrap());
}

// an ABox-only add then flush takes the INCREMENTAL (reduced-ABox) path
// and yields the correct new answer (B(a) contradicts DisjointClasses(A,B)).
#[test]
fn abox_add_uses_incremental_path_and_is_correct() {
    let mut reasoner = IncrementalReasoner::new(base_ontology());
    assert!(reasoner.is_consistent().unwrap());
    // No flush has applied changes yet.
    assert_eq!(reasoner.last_flush_was_incremental(), None);

    // Add B(a): an ABox class assertion over already-present vocabulary (B is in
    // the DisjointClasses TBox axiom), so the incremental path applies.
    reasoner.add_axiom(b_of_a());
    reasoner.flush();

    assert_eq!(
        reasoner.last_flush_was_incremental(),
        Some(true),
        "an ABox-only add over existing vocabulary must take the reduced-ABox incremental path"
    );
    assert!(
        !reasoner.is_consistent().unwrap(),
        "after the incremental flush the added B(a) makes A/B disjointness contradicted"
    );
}

// a TBox add forces the full-rebuild fallback and still gives the correct
// answer. SubClassOf(A,B) is a TBox change; combined with DisjointClasses(A,B)
// and A(a) it makes the ontology inconsistent (a -> A -> B and A/B disjoint).
#[test]
fn tbox_add_forces_full_rebuild_and_is_correct() {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");

    let mut reasoner = IncrementalReasoner::new(base_ontology());
    assert!(reasoner.is_consistent().unwrap());

    reasoner.add_axiom(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a),
        sup: CE::Class(b),
    }));
    reasoner.flush();

    assert_eq!(
        reasoner.last_flush_was_incremental(),
        Some(false),
        "a TBox SubClassOf change must force the full-rebuild fallback"
    );
    assert!(
        !reasoner.is_consistent().unwrap(),
        "A(a) + A ⊑ B + DisjointClasses(A,B) is inconsistent"
    );
}

// removing an ABox fact restores consistency via the incremental path.
#[test]
fn abox_remove_restores_consistency_via_incremental_path() {
    // base + B(a): inconsistent.
    let mut o = base_ontology();
    o.insert(b_of_a());
    let mut reasoner = IncrementalReasoner::new(o);
    assert!(!reasoner.is_consistent().unwrap());

    // Remove the contradicting B(a): an ABox-only change -> incremental path.
    reasoner.remove_axiom(b_of_a());
    reasoner.flush();

    assert_eq!(
        reasoner.last_flush_was_incremental(),
        Some(true),
        "an ABox-only removal must take the reduced-ABox incremental path"
    );
    assert!(
        reasoner.is_consistent().unwrap(),
        "removing B(a) drops the negative fact and restores consistency"
    );
}

// an ontology whose clausification introduces `internal:all#` concepts
// (a transitive property used in a universal restriction) still reasons
// correctly after an incremental ABox addition (the reused TBox clauses are not
// corrupted), and after a TBox addition that itself introduces fresh
// `internal:all#` concepts via `create_delta_dl_ontology` -- whose replacement
// index is threaded off the original atomic-concept count so the fresh concepts
// cannot collide with the original ones (Reasoner.java:2072-2073).
#[test]
fn complex_role_universal_no_internal_all_collision() {
    let build = Build::new_arc();
    let r = build.object_property("http://example.org/r");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let x = build.named_individual("http://example.org/x");
    let y = build.named_individual("http://example.org/y");

    // TBox: r transitive; D ⊑ ∀r.C. The ∀r.C over a transitive (complex) role
    // forces the object-property-inclusion rewriting to mint `internal:all#`
    // concepts during clausification.
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DeclareObjectProperty(DeclareObjectProperty(r.clone())));
    o.insert(Component::DeclareClass(DeclareClass(c.clone())));
    o.insert(Component::DeclareClass(DeclareClass(d.clone())));
    o.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(
        OPE::ObjectProperty(r.clone()),
    )));
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(d.clone()),
        sup: CE::ObjectAllValuesFrom {
            ope: OPE::ObjectProperty(r.clone()),
            bce: Box::new(CE::Class(c.clone())),
        },
    }));
    // ABox: D(x), r(x,y).
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(x.clone()),
    }));
    o.insert(Component::ObjectPropertyAssertion(
        horned_owl::model::ObjectPropertyAssertion {
            ope: OPE::ObjectProperty(r.clone()),
            from: Individual::Named(x.clone()),
            to: Individual::Named(y.clone()),
        },
    ));

    let mut reasoner = IncrementalReasoner::new(o);
    assert!(reasoner.is_consistent().unwrap());
    // The original clausification minted concepts (including `internal:all#`),
    // so the replacement index threaded into any additional clausification is
    // non-trivial -- the replacement index is exercised here.
    assert!(
        reasoner.original_atomic_concept_count() > 0,
        "the ∀(transitive r).C clausification introduces internal concepts"
    );
    // The TBox entails C(y): x is a D, so ∀r.C holds at x, and r(x,y) -> C(y).
    assert!(
        reasoner
            .is_instance_of(y.clone(), CE::Class(c.clone()))
            .unwrap(),
        "D(x) + D ⊑ ∀r.C + r(x,y) entails C(y)"
    );

    // (a) Incremental ABox add: ¬C(y) makes it inconsistent. ABox-only change ->
    // incremental path reusing the original (∀r.C-derived) TBox clauses intact.
    reasoner.add_axiom(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(CE::Class(c.clone()))),
        i: Individual::Named(y.clone()),
    }));
    reasoner.flush();
    assert_eq!(
        reasoner.last_flush_was_incremental(),
        Some(true),
        "an ABox add over existing vocabulary takes the incremental path even with complex roles"
    );
    assert!(
        !reasoner.is_consistent().unwrap(),
        "¬C(y) contradicts the entailed C(y); incremental TBox-clause reuse must be intact"
    );

    // Restore consistency by removing ¬C(y) (incremental again).
    reasoner.remove_axiom(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(CE::Class(c.clone()))),
        i: Individual::Named(y.clone()),
    }));
    reasoner.flush();
    assert!(reasoner.is_consistent().unwrap());

    // (b) TBox add that itself introduces a fresh ∀(complex role).C -- forces the
    // full-rebuild fallback, which runs `create_delta_dl_ontology` with the
    // threaded replacement index for the added axiom. A second transitive role s
    // and E ⊑ ∀s.C, plus E(y) and s(y,z): entails C(z). If the fresh
    // `internal:all#` concepts collided with the original's, this entailment
    // would be wrong.
    let s = build.object_property("http://example.org/s");
    let e = build.class("http://example.org/E");
    let z = build.named_individual("http://example.org/z");
    reasoner.add_axiom(Component::DeclareObjectProperty(DeclareObjectProperty(s.clone())));
    reasoner.add_axiom(Component::DeclareClass(DeclareClass(e.clone())));
    reasoner.add_axiom(Component::TransitiveObjectProperty(TransitiveObjectProperty(
        OPE::ObjectProperty(s.clone()),
    )));
    reasoner.add_axiom(Component::SubClassOf(SubClassOf {
        sub: CE::Class(e.clone()),
        sup: CE::ObjectAllValuesFrom {
            ope: OPE::ObjectProperty(s.clone()),
            bce: Box::new(CE::Class(c.clone())),
        },
    }));
    reasoner.add_axiom(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(e.clone()),
        i: Individual::Named(y.clone()),
    }));
    reasoner.add_axiom(Component::ObjectPropertyAssertion(
        horned_owl::model::ObjectPropertyAssertion {
            ope: OPE::ObjectProperty(s.clone()),
            from: Individual::Named(y.clone()),
            to: Individual::Named(z.clone()),
        },
    ));
    reasoner.flush();
    assert_eq!(
        reasoner.last_flush_was_incremental(),
        Some(false),
        "TBox changes (transitivity + ∀s.C) force the full-rebuild fallback"
    );
    assert!(reasoner.is_consistent().unwrap());
    assert!(
        reasoner
            .is_instance_of(z.clone(), CE::Class(c.clone()))
            .unwrap(),
        "E(y) + E ⊑ ∀s.C + s(y,z) entails C(z); no internal:all# collision"
    );
    // The original ∀r.C reasoning is also still correct.
    assert!(
        reasoner
            .is_instance_of(y.clone(), CE::Class(c.clone()))
            .unwrap(),
        "the original D ⊑ ∀r.C reasoning survives the rebuild"
    );
}

// (3) flush() with no pending changes is a no-op.
#[test]
fn flush_no_pending_changes_is_noop() {
    let mut reasoner = IncrementalReasoner::new(base_ontology());
    assert!(reasoner.pending_changes().is_empty());

    // Establish a baseline answer.
    let before = reasoner.is_consistent().unwrap();
    assert!(before);

    // Flush with nothing pending must not change anything.
    reasoner.flush();
    assert!(reasoner.pending_changes().is_empty());
    assert_eq!(
        reasoner.is_consistent().unwrap(),
        before,
        "flush with no pending changes is a no-op"
    );
}

// apply_changes (bulk) and the pending-additions/removals views mirror Java's
// getPendingAxiomAdditions / getPendingAxiomRemovals.
#[test]
fn bulk_apply_changes_and_pending_views() {
    let mut reasoner = IncrementalReasoner::new(base_ontology());
    let add = b_of_a();
    let remove = {
        let build = Build::new_arc();
        let a = build.class("http://example.org/A");
        let ind_a = build.named_individual("http://example.org/a");
        Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(a),
            i: Individual::Named(ind_a),
        })
    };
    reasoner.apply_changes(vec![
        OntologyChange::Add(add.clone()),
        OntologyChange::Remove(remove.clone()),
    ]);

    // BUFFERING: both still pending.
    assert_eq!(reasoner.pending_changes().len(), 2);
    assert_eq!(reasoner.pending_axiom_additions(), vec![&add]);
    assert_eq!(reasoner.pending_axiom_removals(), vec![&remove]);

    // Before flush, the ontology is unchanged: A(a) still present so still consistent.
    assert!(reasoner.is_consistent().unwrap());

    // After flush: A(a) removed AND B(a) added -> only B(a) on a, consistent.
    reasoner.flush();
    assert!(reasoner.is_consistent().unwrap());
    assert!(reasoner.pending_changes().is_empty());
}

/// FreshEntityPolicy::Disallow makes a query over an undeclared (fresh)
/// entity throw a FreshEntitiesException analogue; the default Allow policy does not.
#[test]
fn fresh_entity_policy_disallow_rejects_fresh_entities() {
    use hermit_rs::configuration::{Configuration, FreshEntityPolicy};
    let b = Build::new_arc();
    let c = b.class("http://example.org/C");
    let a = b.named_individual("http://example.org/a");

    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(c.clone()),
        i: Individual::Named(a.clone()),
    }));

    let fresh_ind = b.named_individual("http://example.org/fresh-ind");
    let fresh_cls = b.class("http://example.org/Fresh");

    // Disallow: fresh individual + fresh class -> Err.
    let mut cfg = Configuration::default();
    cfg.fresh_entity_policy = FreshEntityPolicy::Disallow;
    let mut r = IncrementalReasoner::with_configuration(o.clone(), cfg);
    let res = r.is_instance_of(fresh_ind.clone(), CE::Class(fresh_cls.clone()));
    assert!(res.is_err(), "Disallow must reject fresh entities, got {res:?}");

    // Disallow but all entities defined -> Ok.
    let mut cfg2 = Configuration::default();
    cfg2.fresh_entity_policy = FreshEntityPolicy::Disallow;
    let mut r2 = IncrementalReasoner::with_configuration(o.clone(), cfg2);
    assert!(r2.is_instance_of(a.clone(), CE::Class(c.clone())).is_ok());

    // Default Allow -> Ok even with fresh entities.
    let mut r3 = IncrementalReasoner::new(o);
    assert!(r3.is_instance_of(fresh_ind, CE::Class(fresh_cls)).is_ok());
}

/// the incremental gate is a faithful per-change port. A ClassAssertion
/// over an UNDEFINED individual forces the full path; a Declaration of an
/// already-defined class stays on the incremental path (both reasoning-neutral).
#[test]
fn classassertion_fresh_individual_full_declaration_incremental() {
    let build = Build::new_arc();
    let b = build.class("http://example.org/B");
    let a_cls = build.class("http://example.org/A");

    // (A) ClassAssertion(B, freshIndividual): individual not defined -> full reload.
    let mut r = IncrementalReasoner::new(base_ontology());
    assert!(r.is_consistent().unwrap());
    let fresh = build.named_individual("http://example.org/fresh-ind");
    r.add_axiom(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(b),
        i: Individual::Named(fresh),
    }));
    r.flush();
    assert_eq!(
        r.last_flush_was_incremental(),
        Some(false),
        "ClassAssertion over an undefined individual must force the full path (Java returns false)"
    );

    // (B) Declaration of the already-defined class A -> incremental path.
    let mut r2 = IncrementalReasoner::new(base_ontology());
    assert!(r2.is_consistent().unwrap());
    r2.add_axiom(Component::DeclareClass(DeclareClass(a_cls)));
    r2.flush();
    assert_eq!(
        r2.last_flush_was_incremental(),
        Some(true),
        "a redundant declaration of a defined class stays on the incremental path"
    );
}
