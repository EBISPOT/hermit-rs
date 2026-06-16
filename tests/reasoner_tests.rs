// Full-pipeline test: OWL ontology -> normalization -> clausification -> reasoning.

use horned_owl::model::{
    Build, ClassAssertion, ClassExpression as CE, Component, DisjointClasses, Individual,
    MutableOntology,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner::Reasoner;
use hermit_rs::structural::{
    Configuration, OWLAxioms, OWLAxiomsExpressivity, OWLClausification, OWLNormalization,
};

fn clausify_result(
    ontology: &SetOntology<hermit_rs::structural::A>,
) -> Result<hermit_rs::model::DLOntology, String> {
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology).unwrap();
    let axioms = normalization.into_axioms();
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    OWLClausification::new(Configuration::default())
        .clausify("http://example.org/onto", &axioms, &expressivity)
}

fn clausify(ontology: &SetOntology<hermit_rs::structural::A>) -> hermit_rs::model::DLOntology {
    clausify_result(ontology).unwrap()
}

#[test]
fn disjoint_classes_consistency() {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let ind_a = build.named_individual("http://example.org/a");

    // Base: DisjointClasses(A, B) and A(a).
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind_a.clone()),
    }));

    // A(a) alone with the disjointness is consistent.
    let dl_ontology = clausify(&base);
    assert!(Reasoner::new(&dl_ontology).is_consistent());

    // Adding B(a) makes it inconsistent (A and B are disjoint).
    let mut with_b = base.clone();
    with_b.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(b.clone()),
        i: Individual::Named(ind_a.clone()),
    }));
    let dl_ontology = clausify(&with_b);
    assert!(!Reasoner::new(&dl_ontology).is_consistent());
}

/// Tableau-reuse regression: HermiT's reasoner keeps ONE `m_tableau` for its
/// lifetime, clearing it between satisfiability tests. The Rust port reuses one
/// configured tableau across the ~15 per-test `is_*`/subsumption methods, calling
/// `Tableau::clear()` (which fires `tableauCleared`) between tests. This test runs
/// a SEQUENCE of different subsumption / satisfiability queries through ONE
/// reasoner (so the tableau is built once and then cleared+reused) and asserts
/// every answer matches a from-scratch baseline (a freshly-built reasoner per
/// query). Any cross-test contamination from an incomplete `clear()` would make a
/// reused answer diverge from its from-scratch baseline.
#[test]
fn tableau_reuse_matches_from_scratch_baseline() {
    use hermit_rs::model::AtomicConcept;
    use horned_owl::model::SubClassOf;

    let build = Build::new_arc();
    let iri = |n: &str| format!("http://example.org/{n}");
    let mk = |n: &str| build.class(iri(n));
    let (animal, mammal, dog, cat, pet) =
        (mk("Animal"), mk("Mammal"), mk("Dog"), mk("Cat"), mk("Pet"));

    // A small TBox: Mammal ⊑ Animal, Dog ⊑ Mammal, Cat ⊑ Mammal, Dog ⊑ Pet,
    // and DisjointClasses(Dog, Cat) (so Dog ⊓ Cat is unsatisfiable).
    let mut o: SetOntology<_> = SetOntology::new();
    let mut sub = |s: &horned_owl::model::Class<hermit_rs::structural::A>,
                   p: &horned_owl::model::Class<hermit_rs::structural::A>| {
        o.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(s.clone()),
            sup: CE::Class(p.clone()),
        }));
    };
    sub(&mammal, &animal);
    sub(&dog, &mammal);
    sub(&cat, &mammal);
    sub(&dog, &pet);
    drop(sub);
    o.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(dog.clone()),
        CE::Class(cat.clone()),
    ])));

    let ac = |n: &str| AtomicConcept::create(iri(n));

    // The query sequence: a mix of subsumption (sub ⊑ sup) and satisfiability
    // checks, deliberately interleaved so a leftover assertion from one test
    // would corrupt the next.
    let names = ["Animal", "Mammal", "Dog", "Cat", "Pet"];

    let dl = clausify(&o);

    // Baseline: a fresh reasoner (hence a fresh tableau) per query.
    let baseline_subsumes = |s: &str, p: &str| -> bool {
        let dl = clausify(&o);
        let reasoner = Reasoner::new(&dl);
        let mut manager = reasoner.new_manager();
        reasoner.atomic_subsumes(&mut manager, &ac(s), &ac(p))
    };
    let baseline_satisfiable = |c: &str| -> bool {
        let dl = clausify(&o);
        let reasoner = Reasoner::new(&dl);
        let mut manager = reasoner.new_manager();
        reasoner.atomic_satisfiable(&mut manager, &ac(c))
    };

    // Reused: ONE reasoner + ONE manager; the tableau is built on the first
    // checkout and cleared+reused on every subsequent one.
    let reasoner = Reasoner::new(&dl);
    let mut manager = reasoner.new_manager();

    // Run every ordered pair as a subsumption test, interleaving satisfiability
    // checks, all through the single reused tableau.
    for s in names {
        assert_eq!(
            reasoner.atomic_satisfiable(&mut manager, &ac(s)),
            baseline_satisfiable(s),
            "satisfiability of {s} diverged under tableau reuse",
        );
        for p in names {
            assert_eq!(
                reasoner.atomic_subsumes(&mut manager, &ac(s), &ac(p)),
                baseline_subsumes(s, p),
                "subsumption {s} ⊑ {p} diverged under tableau reuse",
            );
        }
    }

    // Spot-check the expected hierarchy facts directly (so a uniformly-wrong
    // baseline can't hide a bug): Dog ⊑ Animal/Mammal/Pet, Cat ⊑ Animal but
    // Cat ⋢ Pet, and Dog/Cat are each individually satisfiable.
    assert!(reasoner.atomic_subsumes(&mut manager, &ac("Dog"), &ac("Animal")));
    assert!(reasoner.atomic_subsumes(&mut manager, &ac("Dog"), &ac("Pet")));
    assert!(reasoner.atomic_subsumes(&mut manager, &ac("Cat"), &ac("Animal")));
    assert!(!reasoner.atomic_subsumes(&mut manager, &ac("Cat"), &ac("Pet")));
    assert!(reasoner.atomic_satisfiable(&mut manager, &ac("Dog")));
    assert!(reasoner.atomic_satisfiable(&mut manager, &ac("Cat")));

    // And the subsumer read-off (concept_subsumers, the classification path)
    // must agree with a from-scratch read-off after all the reuse churn.
    let reused_dog_subsumers = {
        let mut v: Vec<String> = reasoner
            .concept_subsumers(&mut manager, &ac("Dog"))
            .expect("Dog is satisfiable")
            .into_iter()
            .map(|c| c.iri().to_string())
            .collect();
        v.sort();
        v
    };
    let fresh_dog_subsumers = {
        let dl = clausify(&o);
        let reasoner = Reasoner::new(&dl);
        let mut manager = reasoner.new_manager();
        let mut v: Vec<String> = reasoner
            .concept_subsumers(&mut manager, &ac("Dog"))
            .expect("Dog is satisfiable")
            .into_iter()
            .map(|c| c.iri().to_string())
            .collect();
        v.sort();
        v
    };
    assert_eq!(
        reused_dog_subsumers, fresh_dog_subsumers,
        "Dog's read-off subsumers diverged under tableau reuse",
    );
}

#[test]
fn subclass_chain_propagation_consistency() {
    use horned_owl::model::SubClassOf;
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let ind = build.named_individual("http://example.org/x");

    // A ⊑ B, B ⊑ C, DisjointClasses(A, C), A(x): A(x) -> B(x) -> C(x), and A,C
    // disjoint, so x is both A and C -> inconsistent.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::Class(c.clone()),
    }));
    ontology.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(c.clone()),
    ])));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));
    let dl_ontology = clausify(&ontology);
    assert!(!Reasoner::new(&dl_ontology).is_consistent());
}

#[test]
fn existential_expansion_consistency() {
    use horned_owl::model::{
        ClassAssertion, DisjointClasses, ObjectPropertyExpression, SubClassOf,
    };
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let r = build.object_property("http://example.org/r");
    let ind = build.named_individual("http://example.org/a");

    // A ⊑ ∃r.B, A(a): consistent -- the model has an r-successor of a in B.
    let some_r_b = CE::ObjectSomeValuesFrom {
        ope: ObjectPropertyExpression::ObjectProperty(r.clone()),
        bce: Box::new(CE::Class(b.clone())),
    };
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: some_r_b,
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));
    let dl_ontology = clausify(&base);
    assert!(Reasoner::new(&dl_ontology).is_consistent());

    // Force the fresh B-successor into a contradiction: B ⊑ C and
    // DisjointClasses(B, C). Now A(a) builds a B-successor that must also be C,
    // contradicting the disjointness -> inconsistent.
    let mut contradiction = base.clone();
    contradiction.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::Class(c.clone()),
    }));
    contradiction.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(b.clone()),
        CE::Class(c.clone()),
    ])));
    let dl_ontology = clausify(&contradiction);
    assert!(!Reasoner::new(&dl_ontology).is_consistent());
}

#[test]
fn disjunction_branching_and_backtracking() {
    use horned_owl::model::{ClassAssertion, DisjointClasses, SubClassOf};
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let ind = build.named_individual("http://example.org/a");

    // A ⊑ B ⊔ C, A(a), DisjointClasses(A, B): the B branch clashes (A and B
    // disjoint), so the reasoner must backtrack and pick C -> consistent.
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectUnionOf(vec![CE::Class(b.clone()), CE::Class(c.clone())]),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));
    let dl_ontology = clausify(&base);
    assert!(Reasoner::new(&dl_ontology).is_consistent());

    // Also make C disjoint from A: now both disjuncts clash -> inconsistent.
    let mut both = base.clone();
    both.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(c.clone()),
    ])));
    let dl_ontology = clausify(&both);
    assert!(!Reasoner::new(&dl_ontology).is_consistent());
}

#[test]
fn cyclic_existential_terminates_via_blocking() {
    use horned_owl::model::{ClassAssertion, ObjectPropertyExpression, SubClassOf};
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let r = build.object_property("http://example.org/r");
    let ind = build.named_individual("http://example.org/a");

    // A ⊑ ∃r.A, A(a): an infinite r-chain of A-nodes; blocking must terminate
    // it and report consistent.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom {
            ope: ObjectPropertyExpression::ObjectProperty(r.clone()),
            bce: Box::new(CE::Class(a.clone())),
        },
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));
    let dl_ontology = clausify(&ontology);
    assert!(Reasoner::new(&dl_ontology).is_consistent());
}

#[test]
fn standard_reasoning_tasks() {
    use horned_owl::model::SubClassOf;
    use hermit_rs::reasoner::{is_concept_satisfiable, is_instance_of, is_subsumed_by};

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");

    // TBox: A ⊑ B, B ⊑ C.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::Class(c.clone()),
    }));

    // A is satisfiable; A ⊓ ¬A is not.
    assert!(is_concept_satisfiable(&ontology, CE::Class(a.clone())).unwrap());
    assert!(!is_concept_satisfiable(
        &ontology,
        CE::ObjectIntersectionOf(vec![CE::Class(a.clone()), CE::ObjectComplementOf(Box::new(CE::Class(a.clone())))]),
    )
    .unwrap());

    // Subsumption: A ⊑ C (transitively), but not C ⊑ A.
    assert!(is_subsumed_by(&ontology, CE::Class(a.clone()), CE::Class(c.clone())).unwrap());
    assert!(!is_subsumed_by(&ontology, CE::Class(c.clone()), CE::Class(a.clone())).unwrap());

    // Instance: with A(x), x is an instance of C.
    let x = build.named_individual("http://example.org/x");
    let mut with_x = ontology.clone();
    with_x.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(x.clone()),
    }));
    assert!(is_instance_of(&with_x, x.clone(), CE::Class(c)).unwrap());
    assert!(is_instance_of(&with_x, x.clone(), CE::Class(b.clone())).unwrap());
    // x is not an instance of an unrelated class D.
    let d = build.class("http://example.org/D");
    assert!(!is_instance_of(&with_x, x, CE::Class(d)).unwrap());
}

#[test]
fn at_most_cardinality_merges_successors() {
    use horned_owl::model::{
        ClassAssertion, DifferentIndividuals, ObjectPropertyAssertion, ObjectPropertyExpression,
        SubClassOf,
    };
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let r = build.object_property("http://example.org/r");
    let x = build.named_individual("http://example.org/x");
    let y1 = build.named_individual("http://example.org/y1");
    let y2 = build.named_individual("http://example.org/y2");

    let ope = ObjectPropertyExpression::ObjectProperty(r.clone());

    // A ⊑ ≤1 r.⊤, A(x), r(x,y1), r(x,y2): y1 and y2 must be merged (functional).
    // With y1 ≠ y2 asserted, that merge clashes -> inconsistent.
    let max1 = CE::ObjectMaxCardinality {
        n: 1,
        ope: ope.clone(),
        bce: Box::new(CE::Class(build.class("http://www.w3.org/2002/07/owl#Thing"))),
    };
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: max1,
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(x.clone()),
    }));
    ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(x.clone()),
        to: Individual::Named(y1.clone()),
    }));
    ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope,
        from: Individual::Named(x.clone()),
        to: Individual::Named(y2.clone()),
    }));

    // Without y1 ≠ y2: consistent (y1 and y2 are merged).
    assert!(Reasoner::new(&clausify(&ontology)).is_consistent());

    // With y1 ≠ y2: the forced merge contradicts the inequality -> inconsistent.
    let mut distinct = ontology.clone();
    distinct.insert(Component::DifferentIndividuals(DifferentIndividuals(vec![
        Individual::Named(y1),
        Individual::Named(y2),
    ])));
    assert!(!Reasoner::new(&clausify(&distinct)).is_consistent());
}

#[test]
fn universal_restriction_and_property_axioms() {
    use horned_owl::model::{
        ClassAssertion, DisjointClasses, ObjectPropertyAssertion, ObjectPropertyDomain,
        ObjectPropertyExpression, ObjectPropertyRange, SubClassOf,
    };
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let r = build.object_property("http://example.org/r");
    let x = build.named_individual("http://example.org/x");
    let y = build.named_individual("http://example.org/y");
    let ope = ObjectPropertyExpression::ObjectProperty(r.clone());

    // A ⊑ ∀r.C, A(x), r(x,y): forces C(y). With Disjoint(C,B) and B(y) -> clash.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: ope.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(x.clone()),
    }));
    ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(x.clone()),
        to: Individual::Named(y.clone()),
    }));
    // Consistent on its own (y is C).
    assert!(Reasoner::new(&clausify(&ontology)).is_consistent());

    // B(y) and Disjoint(B,C): now y is both C (forced by ∀) and B -> clash.
    let mut inconsistent = ontology.clone();
    inconsistent.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(b.clone()),
        i: Individual::Named(y.clone()),
    }));
    inconsistent.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(b.clone()),
        CE::Class(c.clone()),
    ])));
    assert!(!Reasoner::new(&clausify(&inconsistent)).is_consistent());

    // Property domain: Domain(r, A), r(x,y), Disjoint(A, B), B(x) -> A(x) from
    // domain contradicts B(x) -> inconsistent.
    let mut domain: SetOntology<_> = SetOntology::new();
    domain.insert(Component::ObjectPropertyDomain(ObjectPropertyDomain {
        ope: ope.clone(),
        ce: CE::Class(a.clone()),
    }));
    domain.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(x.clone()),
        to: Individual::Named(y.clone()),
    }));
    domain.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));
    domain.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(b.clone()),
        i: Individual::Named(x.clone()),
    }));
    assert!(!Reasoner::new(&clausify(&domain)).is_consistent());

    // Property range: Range(r, A), r(x,y), Disjoint(A,B), B(y) -> A(y) from range
    // contradicts B(y) -> inconsistent.
    let mut range: SetOntology<_> = SetOntology::new();
    range.insert(Component::ObjectPropertyRange(ObjectPropertyRange {
        ope: ope.clone(),
        ce: CE::Class(a.clone()),
    }));
    range.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope,
        from: Individual::Named(x),
        to: Individual::Named(y.clone()),
    }));
    range.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));
    range.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(b),
        i: Individual::Named(y),
    }));
    assert!(!Reasoner::new(&clausify(&range)).is_consistent());
}

#[test]
fn equivalent_classes_and_property_hierarchy() {
    use horned_owl::model::{
        ClassAssertion, DisjointClasses, EquivalentClasses, ObjectPropertyAssertion,
        ObjectPropertyExpression, SubObjectPropertyExpression,
        SubObjectPropertyOf,
    };
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let e = build.class("http://example.org/E");
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let x = build.named_individual("http://example.org/x");
    let y = build.named_individual("http://example.org/y");

    // EquivalentClasses(A, B): A(x) -> B(x); with Disjoint(B,C) and C(x) -> clash.
    let mut equiv: SetOntology<_> = SetOntology::new();
    equiv.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));
    equiv.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(x.clone()),
    }));
    assert!(Reasoner::new(&clausify(&equiv)).is_consistent());
    let mut equiv_bad = equiv.clone();
    equiv_bad.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(b.clone()),
        CE::Class(c.clone()),
    ])));
    equiv_bad.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(c.clone()),
        i: Individual::Named(x.clone()),
    }));
    assert!(!Reasoner::new(&clausify(&equiv_bad)).is_consistent());

    // r ⊑ s, r(x,y), Range(s, D), Disjoint(D, E), E(y): r(x,y) -> s(x,y) -> D(y),
    // contradicting E(y) -> inconsistent.
    let mut hierarchy: SetOntology<_> = SetOntology::new();
    hierarchy.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sup: ObjectPropertyExpression::ObjectProperty(s.clone()),
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(
            ObjectPropertyExpression::ObjectProperty(r.clone()),
        ),
    }));
    hierarchy.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ObjectPropertyExpression::ObjectProperty(r.clone()),
        from: Individual::Named(x.clone()),
        to: Individual::Named(y.clone()),
    }));
    hierarchy.insert(Component::ObjectPropertyRange(horned_owl::model::ObjectPropertyRange {
        ope: ObjectPropertyExpression::ObjectProperty(s.clone()),
        ce: CE::Class(d.clone()),
    }));
    hierarchy.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(d.clone()),
        CE::Class(e.clone()),
    ])));
    hierarchy.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(e.clone()),
        i: Individual::Named(y.clone()),
    }));
    assert!(!Reasoner::new(&clausify(&hierarchy)).is_consistent());
}

#[test]
fn same_and_different_individuals() {
    use horned_owl::model::{
        ClassAssertion, DifferentIndividuals, DisjointClasses, SameIndividual,
    };
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let p = build.named_individual("http://example.org/p");
    let q = build.named_individual("http://example.org/q");

    // SameIndividual(p, q), A(p), B(q), Disjoint(A, B): p=q is both A and B -> clash.
    let mut same: SetOntology<_> = SetOntology::new();
    same.insert(Component::SameIndividual(SameIndividual(vec![
        Individual::Named(p.clone()),
        Individual::Named(q.clone()),
    ])));
    same.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(p.clone()),
    }));
    same.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(b.clone()),
        i: Individual::Named(q.clone()),
    }));
    // Without disjointness: consistent (p=q is both A and B, which is fine).
    assert!(Reasoner::new(&clausify(&same)).is_consistent());
    let mut same_bad = same.clone();
    same_bad.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));
    assert!(!Reasoner::new(&clausify(&same_bad)).is_consistent());

    // SameIndividual(p, q) AND DifferentIndividuals(p, q): p=q and p≠q -> clash.
    let mut contradiction: SetOntology<_> = SetOntology::new();
    contradiction.insert(Component::SameIndividual(SameIndividual(vec![
        Individual::Named(p.clone()),
        Individual::Named(q.clone()),
    ])));
    contradiction.insert(Component::DifferentIndividuals(DifferentIndividuals(vec![
        Individual::Named(p),
        Individual::Named(q),
    ])));
    assert!(!Reasoner::new(&clausify(&contradiction)).is_consistent());
}

#[test]
fn unsupported_features_error_gracefully() {
    use hermit_rs::reasoner::is_ontology_consistent;
    use horned_owl::model::{
        ObjectPropertyExpression, SubClassOf, SubObjectPropertyExpression, SubObjectPropertyOf,
        TransitiveObjectProperty,
    };
    let build = Build::new_arc();
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());

    // A lone transitive property (the complex inclusion r∘r⊑r) is handled by the
    // object-property inclusion manager: the pipeline succeeds.
    let mut supported: SetOntology<_> = SetOntology::new();
    supported.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(r_e.clone())));
    assert!(is_ontology_consistent(&supported).unwrap());

    // Combining a transitive property with an inverse-property inclusion
    // (s ⊑ Inv(r)) is now supported (the inverse edges feed r's automaton).
    let mut with_inverse: SetOntology<_> = SetOntology::new();
    with_inverse.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(r_e.clone())));
    with_inverse.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(
            ObjectPropertyExpression::ObjectProperty(s.clone()),
        ),
        sup: ObjectPropertyExpression::InverseObjectProperty(r.clone()),
    }));
    assert!(is_ontology_consistent(&with_inverse).is_ok());

    // Using a non-simple (transitive) property in a cardinality restriction is
    // an OWL 2 DL violation HermiT rejects: a clean Err, not a panic.
    let cls = build.class("http://example.org/X");
    let mut invalid: SetOntology<_> = SetOntology::new();
    invalid.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(r_e.clone())));
    invalid.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(cls.clone()),
        sup: CE::ObjectMaxCardinality {
            n: 1,
            ope: r_e.clone(),
            bce: Box::new(CE::Class(build.class("http://www.w3.org/2002/07/owl#Thing"))),
        },
    }));
    let error = is_ontology_consistent(&invalid).unwrap_err();
    assert!(error.contains("Non-simple property"), "got: {error}");
}

#[test]
fn datatype_constraint_violation() {
    use horned_owl::model::{
        DataPropertyAssertion, DataPropertyRange, DataProperty, DataRange,
        FacetRestriction, Literal,
    };
    use horned_owl::vocab::Facet;
    let build = Build::new_arc();
    let dp = build.data_property("http://example.org/age");
    let a = build.named_individual("http://example.org/a");
    let integer = build.datatype("http://www.w3.org/2001/XMLSchema#integer");

    // Range(age, integer[>= 5]); age(a, "3"^^integer): 3 violates >=5 -> inconsistent.
    let range_ge5 = DataRange::DatatypeRestriction(
        integer.clone(),
        vec![FacetRestriction {
            f: Facet::MinInclusive,
            l: Literal::Datatype {
                literal: "5".to_string(),
                datatype_iri: integer.0.clone(),
            },
        }],
    );
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::DataPropertyRange(DataPropertyRange {
        dp: DataProperty(dp.0.clone()),
        dr: range_ge5,
    }));
    ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype {
            literal: "3".to_string(),
            datatype_iri: integer.0.clone(),
        },
    }));
    assert!(!Reasoner::new(&clausify(&ontology)).is_consistent());

    // A satisfying value (7) is consistent.
    let mut ok: SetOntology<_> = SetOntology::new();
    let range_ge5b = DataRange::DatatypeRestriction(
        integer.clone(),
        vec![FacetRestriction {
            f: Facet::MinInclusive,
            l: Literal::Datatype { literal: "5".to_string(), datatype_iri: integer.0.clone() },
        }],
    );
    ok.insert(Component::DataPropertyRange(DataPropertyRange {
        dp: DataProperty(dp.0.clone()),
        dr: range_ge5b,
    }));
    ok.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a),
        to: Literal::Datatype { literal: "7".to_string(), datatype_iri: integer.0.clone() },
    }));
    assert!(Reasoner::new(&clausify(&ok)).is_consistent());
}

#[test]
fn object_has_value_nominal() {
    use horned_owl::model::{
        ClassAssertion, NegativeObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf,
    };
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let r = build.object_property("http://example.org/r");
    let x = build.named_individual("http://example.org/x");
    let b = build.named_individual("http://example.org/b");
    let ope = ObjectPropertyExpression::ObjectProperty(r.clone());

    // A ⊑ ∃r.{b} (ObjectHasValue(r,b)), A(x): forces r(x,b). With ¬r(x,b) -> clash.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectHasValue { ope: ope.clone(), i: Individual::Named(b.clone()) },
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(x.clone()),
    }));
    // Consistent: r(x,b) is added (the {b} nominal is encoded internally).
    assert!(hermit_rs::reasoner::is_ontology_consistent(&ontology).unwrap());
    // With ¬r(x,b): the forced r(x,b) contradicts it -> inconsistent.
    let mut bad = ontology.clone();
    bad.insert(Component::NegativeObjectPropertyAssertion(NegativeObjectPropertyAssertion {
        ope,
        from: Individual::Named(x),
        to: Individual::Named(b),
    }));
    assert!(!hermit_rs::reasoner::is_ontology_consistent(&bad).unwrap());
}

#[test]
fn functional_data_property_datatype_clash() {
    use horned_owl::model::{
        ClassAssertion, DataProperty, DataRange, FacetRestriction, FunctionalDataProperty, Literal,
        SubClassOf,
    };
    use horned_owl::vocab::Facet;
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let dp = build.data_property("http://example.org/v");
    let ind = build.named_individual("http://example.org/a");
    let integer = build.datatype("http://www.w3.org/2001/XMLSchema#integer");

    let ge5 = DataRange::DatatypeRestriction(
        integer.clone(),
        vec![FacetRestriction {
            f: Facet::MinInclusive,
            l: Literal::Datatype { literal: "5".into(), datatype_iri: integer.0.clone() },
        }],
    );
    let le3 = DataRange::DatatypeRestriction(
        integer.clone(),
        vec![FacetRestriction {
            f: Facet::MaxInclusive,
            l: Literal::Datatype { literal: "3".into(), datatype_iri: integer.0.clone() },
        }],
    );

    // Functional(v), A ⊑ ∃v.integer[>=5], A ⊑ ∃v.integer[<=3], A(a): the single
    // v-successor must be both >=5 and <=3 -> empty -> inconsistent.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::FunctionalDataProperty(FunctionalDataProperty(DataProperty(
        dp.0.clone(),
    ))));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::DataSomeValuesFrom { dp: DataProperty(dp.0.clone()), dr: ge5 },
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::DataSomeValuesFrom { dp: DataProperty(dp.0.clone()), dr: le3 },
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));
    assert!(!Reasoner::new(&clausify(&ontology)).is_consistent());
}

#[test]
fn transitive_role_propagates_universal() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf, TransitiveObjectProperty,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let r = build.object_property("http://example.org/r");
    let ind_a = build.named_individual("http://example.org/a");
    let ind_b = build.named_individual("http://example.org/b");
    let ind_c = build.named_individual("http://example.org/c");
    let ope = ObjectPropertyExpression::ObjectProperty(r.clone());

    // Transitive(r), A ⊑ ∀r.C, Disjoint(C,D), A(a), r(a,b), r(b,c), D(c).
    // Transitivity makes c an r-successor of a, so ∀r.C forces C(c); but c is D
    // and C,D are disjoint -> inconsistent.
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(ope.clone())));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: ope.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind_a.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(ind_a.clone()),
        to: Individual::Named(ind_b.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(ind_b.clone()),
        to: Individual::Named(ind_c.clone()),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(ind_c.clone()),
    }));

    assert!(!is_ontology_consistent(&base).unwrap());

    // Without transitivity, c is not an r-successor of a, so ∀r.C only reaches
    // b: D(c) is fine -> consistent.
    let mut non_transitive = base.clone();
    let trans: horned_owl::model::AnnotatedComponent<_> =
        Component::TransitiveObjectProperty(TransitiveObjectProperty(ope.clone())).into();
    non_transitive.take(&trans);
    assert!(is_ontology_consistent(&non_transitive).unwrap());
}

#[test]
fn role_chain_propagates_universal() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf, SubObjectPropertyOf,
        SubObjectPropertyExpression,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let p = build.object_property("http://example.org/p");
    let q = build.object_property("http://example.org/q");
    let s = build.object_property("http://example.org/s");
    let ind_a = build.named_individual("http://example.org/a");
    let ind_b = build.named_individual("http://example.org/b");
    let ind_c = build.named_individual("http://example.org/c");
    let p_e = ObjectPropertyExpression::ObjectProperty(p.clone());
    let q_e = ObjectPropertyExpression::ObjectProperty(q.clone());
    let s_e = ObjectPropertyExpression::ObjectProperty(s.clone());

    // p ∘ q ⊑ s, A ⊑ ∀s.C, Disjoint(C,D), A(a), p(a,b), q(b,c), D(c).
    // The chain p;q implies s(a,c), so ∀s.C forces C(c) -> clash with D(c).
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![p_e.clone(), q_e.clone()]),
        sup: s_e.clone(),
    }));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: s_e.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind_a.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: p_e.clone(),
        from: Individual::Named(ind_a.clone()),
        to: Individual::Named(ind_b.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: q_e.clone(),
        from: Individual::Named(ind_b.clone()),
        to: Individual::Named(ind_c.clone()),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(ind_c.clone()),
    }));

    assert!(!is_ontology_consistent(&base).unwrap());

    // Drop D(c): now consistent (C(c) is fine).
    let mut without_d = base.clone();
    let d_c: horned_owl::model::AnnotatedComponent<_> = Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(ind_c.clone()),
    })
    .into();
    without_d.take(&d_c);
    assert!(is_ontology_consistent(&without_d).unwrap());
}

#[test]
fn inverse_role_universal_propagates_backwards() {
    use horned_owl::model::{ObjectPropertyExpression, SubClassOf};
    use hermit_rs::reasoner::is_concept_satisfiable;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let r = build.object_property("http://example.org/r");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let inv_r = ObjectPropertyExpression::InverseObjectProperty(r.clone());

    // A ⊑ ∃r.A, A ⊑ ∀Inv(r).C, Disjoint(A,C). A fresh x:A has an r-successor
    // y:A; y's ∀Inv(r).C forces C onto y's r-predecessor x, so x is both A and
    // C -> A is unsatisfiable. (Requires inverse-role reasoning.)
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom { ope: r_e.clone(), bce: Box::new(CE::Class(a.clone())) },
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: inv_r, bce: Box::new(CE::Class(c.clone())) },
    }));
    ontology.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(c.clone()),
    ])));

    assert!(!is_concept_satisfiable(&ontology, CE::Class(a.clone())).unwrap());
}

#[test]
fn forall_propagates_along_inverse_of_complex_role() {
    // N2-5 regression: ∀ along the inverse of a *complex* (chain super-) role.
    // p∘q ⊑ s, InverseObjectProperties(r, s) [so r ≡ s⁻]. p(a,b), q(b,c) ⟹ s(a,c)
    // ⟹ r(c,a). c:∀r.¬D ⟹ ¬D at a; but D(a) ⟹ inconsistent. This requires r's
    // automaton to incorporate the mirror of s's chain automaton.
    use horned_owl::model::{
        ClassAssertion, InverseObjectProperties, ObjectPropertyAssertion, ObjectPropertyExpression,
        SubObjectPropertyExpression, SubObjectPropertyOf,
    };
    let build = Build::new_arc();
    let d = build.class("http://example.org/D");
    let p = build.object_property("http://example.org/p");
    let q = build.object_property("http://example.org/q");
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");
    let c = build.named_individual("http://example.org/c");
    let ope = ObjectPropertyExpression::ObjectProperty;

    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![ope(p.clone()), ope(q.clone())]),
        sup: ope(s.clone()),
    }));
    ontology.insert(Component::InverseObjectProperties(InverseObjectProperties(
        r.clone(),
        s.clone(),
    )));
    ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope(p.clone()),
        from: Individual::Named(a.clone()),
        to: Individual::Named(b.clone()),
    }));
    ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope(q.clone()),
        from: Individual::Named(b.clone()),
        to: Individual::Named(c.clone()),
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectAllValuesFrom {
            ope: ope(r.clone()),
            bce: Box::new(CE::ObjectComplementOf(Box::new(CE::Class(d.clone())))),
        },
        i: Individual::Named(c.clone()),
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(a.clone()),
    }));

    // Use the full pipeline (is_ontology_consistent runs the
    // ObjectPropertyInclusionManager that builds the role automata).
    assert!(!hermit_rs::reasoner::is_ontology_consistent(&ontology).unwrap());
}

#[test]
fn top_gci_fires_on_every_node() {
    // `⊤ ⊑ C` clausifies to `C(X) :- owl:Thing(X)`; it must fire on every node,
    // which requires owl:Thing to be materialized on nodes (HermiT's
    // m_needsThingExtension). With `C ⊑ ⊥` and an individual, the ontology is then
    // inconsistent (everything is C, C is empty).
    use horned_owl::model::{ClassAssertion, SubClassOf};
    let build = Build::new_arc();
    let thing = build.class("http://www.w3.org/2002/07/owl#Thing");
    let nothing = build.class("http://www.w3.org/2002/07/owl#Nothing");
    let c = build.class("http://example.org/C");
    let a = build.named_individual("http://example.org/a");

    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(thing.clone()),
        sup: CE::Class(c.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(c.clone()),
        sup: CE::Class(nothing.clone()),
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(thing.clone()),
        i: Individual::Named(a.clone()),
    }));
    assert!(!hermit_rs::reasoner::is_ontology_consistent(&ontology).unwrap());

    // And `⊤ ⊑ C` alone makes every class a subclass of C (C ≡ owl:Thing).
    let mut o2: SetOntology<_> = SetOntology::new();
    let d = build.class("http://example.org/D");
    o2.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(thing.clone()),
        sup: CE::Class(c.clone()),
    }));
    o2.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(d.clone()),
        sup: CE::Class(d.clone()),
    }));
    assert!(hermit_rs::reasoner::is_subsumed_by(
        &o2,
        CE::Class(d.clone()),
        CE::Class(c.clone())
    )
    .unwrap());
}

#[test]
fn empty_abox_tbox_inconsistency_detected() {
    // `⊤ ⊑ ⊥` with NO individuals: the domain is still non-empty, so this is
    // inconsistent. Requires the fallback node (Tableau.java:307-309).
    use horned_owl::model::SubClassOf;
    let build = Build::new_arc();
    let thing = build.class("http://www.w3.org/2002/07/owl#Thing");
    let nothing = build.class("http://www.w3.org/2002/07/owl#Nothing");
    let mut o: SetOntology<_> = SetOntology::new();
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(thing.clone()),
        sup: CE::Class(nothing.clone()),
    }));
    assert!(!hermit_rs::reasoner::is_ontology_consistent(&o).unwrap());

    let empty: SetOntology<_> = SetOntology::new();
    assert!(hermit_rs::reasoner::is_ontology_consistent(&empty).unwrap());
}

#[test]
fn classify_loads_abox_for_nominals() {
    // B ≡ {a}, A(a)  ⊢  B ⊑ A. The reused classification tableau must load the
    // ABox when the ontology has nominals (HermiT's loadPermanentABox).
    use horned_owl::model::{ClassAssertion, EquivalentClasses};
    use hermit_rs::reasoner::classify;
    let build = Build::new_arc();
    let a_cls = build.class("http://example.org/A");
    let b_cls = build.class("http://example.org/B");
    let a_ind = build.named_individual("http://example.org/a");

    let mut o: SetOntology<_> = SetOntology::new();
    o.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(b_cls.clone()),
        CE::ObjectOneOf(vec![Individual::Named(a_ind.clone())]),
    ])));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a_cls.clone()),
        i: Individual::Named(a_ind.clone()),
    }));

    let h = classify(&o).unwrap();
    let b_node = h.node_for_element(&b_cls).unwrap();
    let a_node = h.node_for_element(&a_cls).unwrap();
    assert!(h.ancestor_nodes(b_node).contains(&a_node));
}

#[test]
fn unsupported_datatype_is_rejected() {
    // An undefined custom datatype is rejected (HermiT's UnsupportedDatatypeException),
    // not silently treated as a vacuous range (which made `D ⊓ ¬D` satisfiable).
    use horned_owl::model::{ClassAssertion, DataProperty};
    let build = Build::new_arc();
    let d = build.datatype("http://example.org/MyType");
    let p = build.data_property("http://example.org/p");
    let a = build.named_individual("http://example.org/a");
    let mut o: SetOntology<_> = SetOntology::new();
    // The custom datatype used in a data range goes through DatatypeRegistry
    // validation, which rejects it (it has no handler and no DatatypeDefinition).
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::DataSomeValuesFrom {
            dp: DataProperty(p.0.clone()),
            dr: horned_owl::model::DataRange::Datatype(d.clone()),
        },
        i: Individual::Named(a.clone()),
    }));
    assert!(hermit_rs::reasoner::is_ontology_consistent(&o).is_err());
}

#[test]
fn ill_typed_literal_is_rejected_at_clausification() {
    // A literal with a malformed LEXICAL form of a SUPPORTED datatype goes through
    // Constant.create -> DatatypeRegistry.parseLiteral, which throws
    // MalformedLiteralException. OWLClausification.getConstant does NOT catch that
    // (it catches only UnsupportedDatatypeException), so HermiT REJECTS the ontology
    // at clausification regardless of ignore_unsupported_datatypes -- it is not
    // loaded-then-inconsistent.
    use horned_owl::model::{DataProperty, DataPropertyAssertion, Literal};
    let build = Build::new_arc();
    let dp = build.data_property("http://example.org/p");
    let a = build.named_individual("http://example.org/a");
    let integer = build.datatype("http://www.w3.org/2001/XMLSchema#integer");

    // p(a, "abc"^^xsd:integer): "abc" is not a valid integer lexical form.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype { literal: "abc".to_string(), datatype_iri: integer.0.clone() },
    }));
    assert!(clausify_result(&ontology).is_err());

    // A well-typed literal clausifies and is consistent.
    let mut ok: SetOntology<_> = SetOntology::new();
    ok.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype { literal: "42".to_string(), datatype_iri: integer.0.clone() },
    }));
    assert!(Reasoner::new(&clausify(&ok)).is_consistent());
}

#[test]
fn unsupported_datatype_literal_rejected_or_anonymized_by_config() {
    // A literal whose datatype is not in the OWL 2 datatype map (and is not an
    // internal:* datatype) is an UnsupportedDatatypeException at clausification.
    // OWLClausification.getConstant *catches* it: by default it rethrows (reject),
    // but under ignoreUnsupportedDatatypes it substitutes an anonymous constant so
    // the ontology loads (and is consistent). (M1-1 / S2-1)
    use horned_owl::model::{DataProperty, DataPropertyAssertion, Literal};
    let build = Build::new_arc();
    let dp = build.data_property("http://example.org/p");
    let a = build.named_individual("http://example.org/a");
    let custom = build.datatype("http://example.org/MyType");

    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype { literal: "v".to_string(), datatype_iri: custom.0.clone() },
    }));

    // Default configuration: the ontology is rejected at clausification.
    assert!(clausify_result(&ontology).is_err());

    // ignore_unsupported_datatypes: clausification succeeds (anonymous constant)
    // and the ontology is consistent.
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(&ontology).unwrap();
    let axioms = normalization.into_axioms();
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    let config = Configuration { ignore_unsupported_datatypes: true, ..Configuration::default() };
    let dl = OWLClausification::new(config)
        .clausify("http://example.org/onto", &axioms, &expressivity)
        .expect("ignore_unsupported_datatypes accepts the unsupported-datatype literal");
    assert!(Reasoner::new(&dl).is_consistent());
}

#[test]
fn internal_datatype_literal_is_never_rejected() {
    // internal:* datatypes (used by the data-property entailment reductions, e.g.
    // internal:anonymous-constants) are always valid: clausification never rejects
    // or anonymizes them, even under the default configuration that rejects other
    // unsupported datatypes. (Guards the data-property reductions; cf. p01d_* tests.)
    use horned_owl::model::{DataProperty, DataPropertyAssertion, Literal};
    let build = Build::new_arc();
    let dp = build.data_property("http://example.org/p");
    let a = build.named_individual("http://example.org/a");

    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype {
            literal: "c1".to_string(),
            datatype_iri: build.iri("internal:anonymous-constants"),
        },
    }));
    // Default config (ignore_unsupported_datatypes = false) still clausifies fine.
    assert!(clausify_result(&ontology).is_ok());
    assert!(Reasoner::new(&clausify(&ontology)).is_consistent());
}

#[test]
fn out_of_range_derived_integer_is_inconsistent() {
    use horned_owl::model::{DataProperty, DataPropertyAssertion, Literal};
    let build = Build::new_arc();
    let dp = build.data_property("http://example.org/p");
    let a = build.named_individual("http://example.org/a");
    let nni = build.datatype("http://www.w3.org/2001/XMLSchema#nonNegativeInteger");

    // p(a, "-1"^^xsd:nonNegativeInteger): -1 is outside the value space -> the
    // literal is ill-typed -> inconsistent.
    let mut bad: SetOntology<_> = SetOntology::new();
    bad.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype { literal: "-1".to_string(), datatype_iri: nni.0.clone() },
    }));
    assert!(!Reasoner::new(&clausify(&bad)).is_consistent());

    // An in-range value is consistent.
    let mut ok: SetOntology<_> = SetOntology::new();
    ok.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype { literal: "0".to_string(), datatype_iri: nni.0.clone() },
    }));
    assert!(Reasoner::new(&clausify(&ok)).is_consistent());
}

#[test]
fn datetime_facet_violation_is_inconsistent() {
    use horned_owl::model::{
        DataProperty, DataPropertyAssertion, DataPropertyRange, DataRange, FacetRestriction,
        Literal,
    };
    use horned_owl::vocab::Facet;
    let build = Build::new_arc();
    let dp = build.data_property("http://example.org/when");
    let a = build.named_individual("http://example.org/a");
    let date_time = build.datatype("http://www.w3.org/2001/XMLSchema#dateTime");

    // Range(when, dateTime[>= 2020-01-01T00:00:00Z]); when(a, 2019-06-15T...Z):
    // the value precedes the minimum -> inconsistent.
    let range = DataRange::DatatypeRestriction(
        date_time.clone(),
        vec![FacetRestriction {
            f: Facet::MinInclusive,
            l: Literal::Datatype {
                literal: "2020-01-01T00:00:00Z".to_string(),
                datatype_iri: date_time.0.clone(),
            },
        }],
    );
    let mut bad: SetOntology<_> = SetOntology::new();
    bad.insert(Component::DataPropertyRange(DataPropertyRange {
        dp: DataProperty(dp.0.clone()),
        dr: range.clone(),
    }));
    bad.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype {
            literal: "2019-06-15T12:00:00Z".to_string(),
            datatype_iri: date_time.0.clone(),
        },
    }));
    assert!(!Reasoner::new(&clausify(&bad)).is_consistent());

    // A value at/after the minimum is consistent.
    let mut ok: SetOntology<_> = SetOntology::new();
    ok.insert(Component::DataPropertyRange(DataPropertyRange {
        dp: DataProperty(dp.0.clone()),
        dr: range,
    }));
    ok.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype {
            literal: "2021-03-01T00:00:00Z".to_string(),
            datatype_iri: date_time.0.clone(),
        },
    }));
    assert!(Reasoner::new(&clausify(&ok)).is_consistent());
}

#[test]
fn at_most_two_with_three_distinct_successors_is_inconsistent() {
    use horned_owl::model::{
        ClassAssertion, DifferentIndividuals, ObjectPropertyAssertion, ObjectPropertyExpression,
        SubClassOf,
    };
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let r = build.object_property("http://example.org/r");
    let x = build.named_individual("http://example.org/x");
    let y1 = build.named_individual("http://example.org/y1");
    let y2 = build.named_individual("http://example.org/y2");
    let y3 = build.named_individual("http://example.org/y3");
    let ope = ObjectPropertyExpression::ObjectProperty(r.clone());

    // A ⊑ ≤2 r.⊤, A(x), r(x, y1..y3), all three y distinct: three distinct
    // r-successors cannot fit under ≤2 -> inconsistent (exercises the at-most
    // n>1 disjunctive branching over the candidate merges).
    let max2 = CE::ObjectMaxCardinality {
        n: 2,
        ope: ope.clone(),
        bce: Box::new(CE::Class(build.class("http://www.w3.org/2002/07/owl#Thing"))),
    };
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: max2,
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(x.clone()),
    }));
    for y in [&y1, &y2, &y3] {
        ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope: ope.clone(),
            from: Individual::Named(x.clone()),
            to: Individual::Named(y.clone()),
        }));
    }
    // Without distinctness: consistent (two of them can merge).
    assert!(Reasoner::new(&clausify(&ontology)).is_consistent());

    ontology.insert(Component::DifferentIndividuals(DifferentIndividuals(vec![
        Individual::Named(y1.clone()),
        Individual::Named(y2.clone()),
        Individual::Named(y3.clone()),
    ])));
    assert!(!Reasoner::new(&clausify(&ontology)).is_consistent());
}

#[test]
fn entailment_checker() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SameIndividual, SubClassOf,
    };
    use hermit_rs::reasoner::is_entailed;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let r = build.object_property("http://example.org/r");
    let x = build.named_individual("http://example.org/x");
    let y = build.named_individual("http://example.org/y");
    let ope = ObjectPropertyExpression::ObjectProperty(r.clone());

    // A ⊑ B, B ⊑ C.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::Class(c.clone()),
    }));

    // Entailed: A ⊑ C (transitively). Not entailed: C ⊑ A.
    assert!(is_entailed(
        &ontology,
        &Component::SubClassOf(SubClassOf { sub: CE::Class(a.clone()), sup: CE::Class(c.clone()) })
    )
    .unwrap());
    assert!(!is_entailed(
        &ontology,
        &Component::SubClassOf(SubClassOf { sub: CE::Class(c.clone()), sup: CE::Class(a.clone()) })
    )
    .unwrap());

    // Class assertion entailment: A(x) -> C(x) is entailed.
    let mut with_x = ontology.clone();
    with_x.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(x.clone()),
    }));
    assert!(is_entailed(
        &with_x,
        &Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(c.clone()),
            i: Individual::Named(x.clone()),
        })
    )
    .unwrap());

    // Property assertion + functional -> SameIndividual entailment.
    let mut props = SetOntology::new();
    props.insert(Component::FunctionalObjectProperty(
        horned_owl::model::FunctionalObjectProperty(ope.clone()),
    ));
    props.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(x.clone()),
        to: Individual::Named(y.clone()),
    }));
    let z = build.named_individual("http://example.org/z");
    props.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(x.clone()),
        to: Individual::Named(z.clone()),
    }));
    // r functional and r(x,y), r(x,z) -> y = z is entailed.
    assert!(is_entailed(
        &props,
        &Component::SameIndividual(SameIndividual(vec![
            Individual::Named(y.clone()),
            Individual::Named(z.clone()),
        ]))
    )
    .unwrap());
}

#[test]
fn explanation_finds_minimal_justification() {
    use horned_owl::model::SubClassOf;
    use hermit_rs::reasoner::explain;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let e = build.class("http://example.org/E");

    let sub = |x: &horned_owl::model::Class<_>, y: &horned_owl::model::Class<_>| {
        Component::SubClassOf(SubClassOf { sub: CE::Class(x.clone()), sup: CE::Class(y.clone()) })
    };

    // A ⊑ B, B ⊑ C (relevant), and D ⊑ E (irrelevant noise).
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(sub(&a, &b));
    ontology.insert(sub(&b, &c));
    ontology.insert(sub(&d, &e));

    // Justification for A ⊑ C is exactly {A ⊑ B, B ⊑ C}.
    let justification = explain(&ontology, &sub(&a, &c)).unwrap().unwrap();
    assert_eq!(justification.len(), 2);
    assert!(justification.contains(&sub(&a, &b)));
    assert!(justification.contains(&sub(&b, &c)));
    assert!(!justification.contains(&sub(&d, &e)));

    // A non-entailed axiom has no justification.
    assert!(explain(&ontology, &sub(&c, &a)).unwrap().is_none());
}

#[test]
fn all_explanations_finds_every_justification() {
    use horned_owl::model::SubClassOf;
    use hermit_rs::reasoner::all_explanations;

    let build = Build::new_arc();
    let cls = |n: &str| build.class(format!("http://example.org/{n}"));
    let (a, b, c, d, e) = (cls("A"), cls("B"), cls("C"), cls("D"), cls("E"));
    let sub = |x: &horned_owl::model::Class<_>, y: &horned_owl::model::Class<_>| {
        Component::SubClassOf(SubClassOf { sub: CE::Class(x.clone()), sup: CE::Class(y.clone()) })
    };

    // Two independent derivations of A ⊑ C: via B and via D; E ⊑ C is noise.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(sub(&a, &b));
    ontology.insert(sub(&b, &c));
    ontology.insert(sub(&a, &d));
    ontology.insert(sub(&d, &c));
    ontology.insert(sub(&e, &c));

    let justifications = all_explanations(&ontology, &sub(&a, &c)).unwrap();
    // Exactly two minimal justifications: {A⊑B,B⊑C} and {A⊑D,D⊑C}.
    assert_eq!(justifications.len(), 2);
    let has = |j: &Vec<Component<_>>, x: &Component<_>| j.contains(x);
    assert!(justifications.iter().any(|j| has(j, &sub(&a, &b)) && has(j, &sub(&b, &c))));
    assert!(justifications.iter().any(|j| has(j, &sub(&a, &d)) && has(j, &sub(&d, &c))));
    // The noise axiom is in no justification.
    assert!(justifications.iter().all(|j| !has(j, &sub(&e, &c))));

    // A non-entailed axiom yields no justifications.
    assert!(all_explanations(&ontology, &sub(&c, &a)).unwrap().is_empty());
}

#[test]
fn cyclic_existential_with_inverse_roles_present_terminates() {
    use horned_owl::model::{InverseObjectProperties, ObjectPropertyExpression, SubClassOf};
    use hermit_rs::reasoner::is_concept_satisfiable;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());

    // A ⊑ ∃r.A with an inverse-role axiom present (enabling validated blocking).
    // The cyclic A-chain's blocks are sound, so the validator keeps them and the
    // computation terminates -> A is satisfiable.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom { ope: r_e.clone(), bce: Box::new(CE::Class(a.clone())) },
    }));
    ontology.insert(Component::InverseObjectProperties(InverseObjectProperties(
        r.clone(),
        s.clone(),
    )));

    assert!(is_concept_satisfiable(&ontology, CE::Class(a.clone())).unwrap());
}

#[test]
fn cyclic_inverse_backward_universal_terminates() {
    use horned_owl::model::{ObjectPropertyExpression, SubClassOf};
    use hermit_rs::reasoner::is_concept_satisfiable;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let r = build.object_property("http://example.org/r");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let inv_r = ObjectPropertyExpression::InverseObjectProperty(r.clone());

    // A ⊑ ∃r.A, A ⊑ ∀Inv(r).C: C propagates backwards along the inverse role.
    // Validated (core-label) blocking terminates this -> A is satisfiable.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom { ope: r_e.clone(), bce: Box::new(CE::Class(a.clone())) },
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: inv_r, bce: Box::new(CE::Class(c.clone())) },
    }));
    assert!(is_concept_satisfiable(&ontology, CE::Class(a.clone())).unwrap());
}

#[test]
fn symmetric_transitive_role_propagates_universal() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf, SymmetricObjectProperty,
        TransitiveObjectProperty,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let r = build.object_property("http://example.org/r");
    let ind_a = build.named_individual("http://example.org/a");
    let ind_b = build.named_individual("http://example.org/b");
    let ope = ObjectPropertyExpression::ObjectProperty(r.clone());

    // Symmetric + Transitive r, A ⊑ ∀r.C, Disjoint(C,D), A(a), r(b,a), D(b).
    // Symmetry makes r(a,b) hold, so ∀r.C forces C(b); but b is D and C,D are
    // disjoint -> inconsistent. (Requires symmetric reasoning combined with the
    // transitivity automaton.)
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::SymmetricObjectProperty(SymmetricObjectProperty(ope.clone())));
    base.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(ope.clone())));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: ope.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind_a.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(ind_b.clone()),
        to: Individual::Named(ind_a.clone()),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(ind_b.clone()),
    }));
    assert!(!is_ontology_consistent(&base).unwrap());

    // Without symmetry (transitive only), r(b,a) does not give a an r-successor
    // b, so ∀r.C never reaches b -> consistent.
    let mut non_symmetric = base.clone();
    let sym: horned_owl::model::AnnotatedComponent<_> =
        Component::SymmetricObjectProperty(SymmetricObjectProperty(ope.clone())).into();
    non_symmetric.take(&sym);
    assert!(is_ontology_consistent(&non_symmetric).unwrap());
}

#[test]
fn universal_over_inverse_of_transitive_role() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf, TransitiveObjectProperty,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let start = build.class("http://example.org/Start");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let r = build.object_property("http://example.org/r");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let inv_r = ObjectPropertyExpression::InverseObjectProperty(r.clone());
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");
    let z = build.named_individual("http://example.org/z");

    // Transitive r, r(a,b), r(b,z), Start(z), Start ⊑ ∀Inv(r).C, Disjoint(C,D),
    // D(a). Transitivity gives r(a,z), so z's Inv(r)-successors include a, which
    // ∀Inv(r).C forces into C; a is D and C,D disjoint -> inconsistent.
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(r_e.clone())));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(start.clone()),
        sup: CE::ObjectAllValuesFrom { ope: inv_r, bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(start.clone()),
        i: Individual::Named(z.clone()),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(a.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: r_e.clone(),
        from: Individual::Named(a.clone()),
        to: Individual::Named(b.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: r_e.clone(),
        from: Individual::Named(b.clone()),
        to: Individual::Named(z.clone()),
    }));
    assert!(!is_ontology_consistent(&base).unwrap());

    // Without transitivity, z has no r-predecessor a (only b), so a is not
    // forced into C -> consistent.
    let mut non_transitive = base.clone();
    let trans: horned_owl::model::AnnotatedComponent<_> =
        Component::TransitiveObjectProperty(TransitiveObjectProperty(r_e.clone())).into();
    non_transitive.take(&trans);
    assert!(is_ontology_consistent(&non_transitive).unwrap());
}

#[test]
fn genuine_inverse_inclusion_with_simple_roles_alongside_complex() {
    use horned_owl::model::{
        NegativeObjectPropertyAssertion, ObjectPropertyAssertion, ObjectPropertyExpression,
        SubObjectPropertyExpression, SubObjectPropertyOf, TransitiveObjectProperty,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let t = build.object_property("http://example.org/t");
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let inv_s = ObjectPropertyExpression::InverseObjectProperty(s.clone());

    // A transitive t (a complex inclusion, so the inclusion manager runs) plus a
    // genuine inverse inclusion r ⊑ Inv(s) over the *simple* roles r, s. The
    // inverse inclusion is clausified directly, so r(a,b) entails s(b,a):
    // asserting ¬s(b,a) is inconsistent.
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(
        ObjectPropertyExpression::ObjectProperty(t.clone()),
    )));
    base.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(r_e.clone()),
        sup: inv_s.clone(),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: r_e.clone(),
        from: Individual::Named(a.clone()),
        to: Individual::Named(b.clone()),
    }));

    let mut inconsistent = base.clone();
    inconsistent.insert(Component::NegativeObjectPropertyAssertion(
        NegativeObjectPropertyAssertion {
            ope: ObjectPropertyExpression::ObjectProperty(s.clone()),
            from: Individual::Named(b.clone()),
            to: Individual::Named(a.clone()),
        },
    ));
    assert!(!is_ontology_consistent(&inconsistent).unwrap());

    // Without the negative assertion, it is consistent (and no error).
    assert!(is_ontology_consistent(&base).unwrap());
}

#[test]
fn role_chain_with_inverse_subproperty() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf, SubObjectPropertyExpression,
        SubObjectPropertyOf,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let p = build.object_property("http://example.org/p");
    let q = build.object_property("http://example.org/q");
    let r = build.object_property("http://example.org/r");
    let p_e = ObjectPropertyExpression::ObjectProperty(p.clone());
    let q_e = ObjectPropertyExpression::ObjectProperty(q.clone());
    let inv_q = ObjectPropertyExpression::InverseObjectProperty(q.clone());
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let ind_a = build.named_individual("http://example.org/a");
    let m = build.named_individual("http://example.org/m");
    let z = build.named_individual("http://example.org/z");

    // p ∘ Inv(q) ⊑ r, A ⊑ ∀r.C, Disjoint(C,D), A(a), p(a,m), q(z,m), D(z).
    // p(a,m) ∧ Inv(q)(m,z) [= q(z,m)] -> r(a,z), so ∀r.C forces C(z); z is D and
    // C,D disjoint -> inconsistent.
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![p_e.clone(), inv_q.clone()]),
        sup: r_e.clone(),
    }));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: r_e.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind_a.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: p_e.clone(),
        from: Individual::Named(ind_a.clone()),
        to: Individual::Named(m.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: q_e.clone(),
        from: Individual::Named(z.clone()),
        to: Individual::Named(m.clone()),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(z.clone()),
    }));
    assert!(!is_ontology_consistent(&base).unwrap());

    // Without the q(z,m) edge, z is not an r-successor of a -> consistent.
    let mut without_q = base.clone();
    let q_edge: horned_owl::model::AnnotatedComponent<_> =
        Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope: q_e.clone(),
            from: Individual::Named(z.clone()),
            to: Individual::Named(m.clone()),
        })
        .into();
    without_q.take(&q_edge);
    assert!(is_ontology_consistent(&without_q).unwrap());
}

#[test]
fn role_chain_with_inverse_of_transitive_subproperty() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf, SubObjectPropertyExpression,
        SubObjectPropertyOf, TransitiveObjectProperty,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let p = build.object_property("http://example.org/p");
    let q = build.object_property("http://example.org/q");
    let r = build.object_property("http://example.org/r");
    let p_e = ObjectPropertyExpression::ObjectProperty(p.clone());
    let q_e = ObjectPropertyExpression::ObjectProperty(q.clone());
    let inv_q = ObjectPropertyExpression::InverseObjectProperty(q.clone());
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let a_i = build.named_individual("http://example.org/a");
    let y = build.named_individual("http://example.org/y");
    let w = build.named_individual("http://example.org/w");
    let zz = build.named_individual("http://example.org/zz");

    // Transitive q, p ∘ Inv(q) ⊑ r, A ⊑ ∀r.C, Disjoint(C,D), A(a), p(a,y),
    // q(w,y), q(zz,w), D(zz). Transitivity gives q(zz,y) = Inv(q)(y,zz), so the
    // chain gives r(a,zz); ∀r.C forces C(zz), clashing with D(zz). Requires the
    // inverse of a *complex* (transitive) property in the chain -- the mirrored
    // automaton substitution.
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(q_e.clone())));
    base.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![p_e.clone(), inv_q.clone()]),
        sup: r_e.clone(),
    }));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: r_e.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(a_i.clone()),
    }));
    let edge = |ope: &ObjectPropertyExpression<hermit_rs::structural::A>,
                f: &horned_owl::model::NamedIndividual<hermit_rs::structural::A>,
                t: &horned_owl::model::NamedIndividual<hermit_rs::structural::A>| {
        Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope: ope.clone(),
            from: Individual::Named(f.clone()),
            to: Individual::Named(t.clone()),
        })
    };
    base.insert(edge(&p_e, &a_i, &y));
    base.insert(edge(&q_e, &w, &y));
    base.insert(edge(&q_e, &zz, &w));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(zz.clone()),
    }));
    assert!(!is_ontology_consistent(&base).unwrap());

    // Without transitivity of q, q(zz,y) does not hold, so r(a,zz) is not
    // derived -> consistent.
    let mut non_transitive = base.clone();
    let trans: horned_owl::model::AnnotatedComponent<_> =
        Component::TransitiveObjectProperty(TransitiveObjectProperty(q_e.clone())).into();
    non_transitive.take(&trans);
    assert!(is_ontology_consistent(&non_transitive).unwrap());
}

#[test]
fn equivalent_property_shares_complex_automaton() {
    use horned_owl::model::{
        EquivalentObjectProperties, ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf,
        TransitiveObjectProperty,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let s_e = ObjectPropertyExpression::ObjectProperty(s.clone());
    let a_i = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");
    let cc = build.named_individual("http://example.org/cc");

    // Transitive r, r ≡ s, A ⊑ ∀s.C, Disjoint(C,D), A(a), r(a,b), r(b,cc), D(cc).
    // s shares r's transitivity automaton (equivalence), and r ≡ s materialises
    // s(a,b), s(b,cc); so ∀s.C propagates transitively to cc, forcing C(cc),
    // which clashes with D(cc).
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(r_e.clone())));
    base.insert(Component::EquivalentObjectProperties(EquivalentObjectProperties(vec![
        r_e.clone(),
        s_e.clone(),
    ])));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: s_e.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(a_i.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: r_e.clone(),
        from: Individual::Named(a_i.clone()),
        to: Individual::Named(b.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: r_e.clone(),
        from: Individual::Named(b.clone()),
        to: Individual::Named(cc.clone()),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(cc.clone()),
    }));
    assert!(!is_ontology_consistent(&base).unwrap());

    // Without transitivity of r, ∀s.C only reaches b (one step) -> consistent.
    let mut non_transitive = base.clone();
    let trans: horned_owl::model::AnnotatedComponent<_> =
        Component::TransitiveObjectProperty(TransitiveObjectProperty(r_e.clone())).into();
    non_transitive.take(&trans);
    assert!(is_ontology_consistent(&non_transitive).unwrap());
}

#[test]
fn role_chain_with_inverse_super_property() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf, SubObjectPropertyExpression,
        SubObjectPropertyOf,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let p = build.object_property("http://example.org/p");
    let q = build.object_property("http://example.org/q");
    let r = build.object_property("http://example.org/r");
    let p_e = ObjectPropertyExpression::ObjectProperty(p.clone());
    let q_e = ObjectPropertyExpression::ObjectProperty(q.clone());
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let inv_r = ObjectPropertyExpression::InverseObjectProperty(r.clone());
    let x = build.named_individual("http://example.org/x");
    let y = build.named_individual("http://example.org/y");
    let znode = build.named_individual("http://example.org/znode");

    // p ∘ q ⊑ Inv(r) [≡ Inv(q) ∘ Inv(p) ⊑ r], A ⊑ ∀r.C, Disjoint(C,D),
    // A(znode), p(x,y), q(y,znode), D(x). The chain gives Inv(r)(x,znode) =
    // r(znode,x), so ∀r.C on znode forces C(x); x is D -> clash.
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![p_e.clone(), q_e.clone()]),
        sup: inv_r.clone(),
    }));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: r_e.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(znode.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: p_e.clone(),
        from: Individual::Named(x.clone()),
        to: Individual::Named(y.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: q_e.clone(),
        from: Individual::Named(y.clone()),
        to: Individual::Named(znode.clone()),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(x.clone()),
    }));
    assert!(!is_ontology_consistent(&base).unwrap());

    // Drop the q edge: no chain, so x is not an r-target of znode -> consistent.
    let mut without_q = base.clone();
    let q_edge: horned_owl::model::AnnotatedComponent<_> =
        Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope: q_e.clone(),
            from: Individual::Named(y.clone()),
            to: Individual::Named(znode.clone()),
        })
        .into();
    without_q.take(&q_edge);
    assert!(is_ontology_consistent(&without_q).unwrap());
}

#[test]
fn genuine_inverse_inclusion_touching_transitive_role() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf, SubObjectPropertyExpression,
        SubObjectPropertyOf, TransitiveObjectProperty,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let s_e = ObjectPropertyExpression::ObjectProperty(s.clone());
    let inv_s = ObjectPropertyExpression::InverseObjectProperty(s.clone());
    let znode = build.named_individual("http://example.org/zn");
    let an = build.named_individual("http://example.org/an");
    let bn = build.named_individual("http://example.org/bn");

    // Transitive s, r ⊑ Inv(s), A ⊑ ∀s.C, Disjoint(C,D), A(zn), r(an,zn),
    // r(bn,an), D(bn). r(an,zn) -> s(zn,an); r(bn,an) -> s(an,bn); transitivity
    // gives s(zn,bn); so ∀s.C on zn forces C(bn), clashing with D(bn).
    let edge = |ope: &ObjectPropertyExpression<hermit_rs::structural::A>,
                f: &horned_owl::model::NamedIndividual<hermit_rs::structural::A>,
                t: &horned_owl::model::NamedIndividual<hermit_rs::structural::A>| {
        Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope: ope.clone(),
            from: Individual::Named(f.clone()),
            to: Individual::Named(t.clone()),
        })
    };
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(s_e.clone())));
    base.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(r_e.clone()),
        sup: inv_s.clone(),
    }));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: s_e.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(znode.clone()),
    }));
    base.insert(edge(&r_e, &an, &znode));
    base.insert(edge(&r_e, &bn, &an));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(bn.clone()),
    }));
    assert!(!is_ontology_consistent(&base).unwrap());

    // Without transitivity of s, s(zn,bn) is not derived -> consistent.
    let mut non_transitive = base.clone();
    let trans: horned_owl::model::AnnotatedComponent<_> =
        Component::TransitiveObjectProperty(TransitiveObjectProperty(s_e.clone())).into();
    non_transitive.take(&trans);
    assert!(is_ontology_consistent(&non_transitive).unwrap());
}

#[test]
fn swrl_rule_inference() {
    use horned_owl::model::{
        Atom as SwrlAtom, ClassAssertion, IArgument, ObjectPropertyAssertion,
        ObjectPropertyExpression, Rule, Variable as SwrlVar,
    };
    use hermit_rs::reasoner::is_instance_of;

    let build = Build::new_arc();
    let person = build.class("http://example.org/Person");
    let parent = build.object_property("http://example.org/parent");
    let ancestor = build.object_property("http://example.org/ancestor");
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");
    let x = SwrlVar(build.iri("urn:swrl#x"));
    let y = SwrlVar(build.iri("urn:swrl#y"));
    let parent_e = ObjectPropertyExpression::ObjectProperty(parent.clone());
    let ancestor_e = ObjectPropertyExpression::ObjectProperty(ancestor.clone());

    // Rule: parent(x,y) -> ancestor(x,y). With parent(a,b), a:Person, b:Person.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::Rule(Rule {
        body: vec![SwrlAtom::ObjectPropertyAtom {
            pred: parent_e.clone(),
            args: (IArgument::Variable(x.clone()), IArgument::Variable(y.clone())),
        }],
        head: vec![SwrlAtom::ObjectPropertyAtom {
            pred: ancestor_e.clone(),
            args: (IArgument::Variable(x.clone()), IArgument::Variable(y.clone())),
        }],
    }));
    ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: parent_e,
        from: Individual::Named(a.clone()),
        to: Individual::Named(b.clone()),
    }));
    for ind in [&a, &b] {
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(person.clone()),
            i: Individual::Named(ind.clone()),
        }));
    }

    // The rule (DL-safe over the named individuals) entails ancestor(a,b), so a
    // is an instance of ∃ancestor.Person.
    let some_ancestor_person = CE::ObjectSomeValuesFrom {
        ope: ObjectPropertyExpression::ObjectProperty(ancestor.clone()),
        bce: Box::new(CE::Class(person.clone())),
    };
    assert!(is_instance_of(&ontology, a.clone(), some_ancestor_person.clone()).unwrap());
    // b has no ancestor asserted, so b is not such an instance.
    assert!(!is_instance_of(&ontology, b.clone(), some_ancestor_person).unwrap());
}

#[test]
fn at_least_over_small_datatype_is_inconsistent() {
    use horned_owl::model::{ClassAssertion, DataProperty, DataRange, SubClassOf};
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let dp = build.data_property("http://example.org/flag");
    let boolean = build.datatype("http://www.w3.org/2001/XMLSchema#boolean");
    let ind = build.named_individual("http://example.org/a");

    let at_least = |n: u32| CE::DataMinCardinality {
        n,
        dp: DataProperty(dp.0.clone()),
        dr: DataRange::Datatype(boolean.clone()),
    };
    let with = |sup: CE<_>| {
        let mut o: SetOntology<_> = SetOntology::new();
        o.insert(Component::SubClassOf(SubClassOf { sub: CE::Class(a.clone()), sup }));
        o.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(a.clone()),
            i: Individual::Named(ind.clone()),
        }));
        o
    };

    // A \u2291 \u22653 flag.boolean, A(a): three distinct boolean values are required but
    // xsd:boolean has only two -> inconsistent.
    assert!(!Reasoner::new(&clausify(&with(at_least(3)))).is_consistent());
    // \u22652 flag.boolean is satisfiable (two distinct boolean values exist).
    assert!(Reasoner::new(&clausify(&with(at_least(2)))).is_consistent());
}

#[test]
fn bottom_object_property_is_empty() {
    // Regression: the built-in property manager must run in the pipeline so that
    // owl:bottomObjectProperty gets its built-in meaning (∀bottom.Nothing on
    // owl:Thing). Any assertion over it forces the target into owl:Nothing.
    use horned_owl::model::{ObjectPropertyAssertion, ObjectPropertyExpression};
    use hermit_rs::reasoner::is_ontology_consistent;
    let build = Build::new_arc();
    let bottom = build.object_property("http://www.w3.org/2002/07/owl#bottomObjectProperty");
    let r = build.object_property("http://example.org/r");
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");

    let mut with_bottom: SetOntology<_> = SetOntology::new();
    with_bottom.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ObjectPropertyExpression::ObjectProperty(bottom),
        from: Individual::Named(a.clone()),
        to: Individual::Named(b.clone()),
    }));
    assert!(!is_ontology_consistent(&with_bottom).unwrap());

    // Control: the same assertion over an ordinary property is consistent.
    let mut with_ordinary: SetOntology<_> = SetOntology::new();
    with_ordinary.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ObjectPropertyExpression::ObjectProperty(r),
        from: Individual::Named(a),
        to: Individual::Named(b),
    }));
    assert!(is_ontology_consistent(&with_ordinary).unwrap());
}

#[test]
fn empty_conjunction_of_infinite_datatype_ranges() {
    // Regression: the open-world datatype conjunction-emptiness check must seed a
    // derived integer datatype's implicit bounds. Neither range here is finite
    // (so the per-range value_space_size cannot decide), but their conjunction
    // nonNegativeInteger ([0,+INF)) ⊓ integer[<= -1] is empty.
    use horned_owl::model::{
        ClassAssertion, DataProperty, DataRange, FacetRestriction, Literal, SubClassOf,
    };
    use horned_owl::vocab::Facet;
    use hermit_rs::reasoner::is_ontology_consistent;
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let dp = build.data_property("http://example.org/p");
    let ind = build.named_individual("http://example.org/a");
    let nonneg = build.datatype("http://www.w3.org/2001/XMLSchema#nonNegativeInteger");
    let integer = build.datatype("http://www.w3.org/2001/XMLSchema#integer");

    // integer[<= -1]
    let le_minus_one = DataRange::DatatypeRestriction(
        integer.clone(),
        vec![FacetRestriction {
            f: Facet::MaxInclusive,
            l: Literal::Datatype {
                literal: "-1".to_string(),
                datatype_iri: integer.0.clone(),
            },
        }],
    );

    // A ⊑ ∃p.<exists_range>, A ⊑ ∀p.(integer[<= -1]), A(a): the fresh data node
    // gets both ranges, so their conjunction is checked for emptiness.
    let build_onto = |exists_range: DataRange<_>| {
        let mut o: SetOntology<_> = SetOntology::new();
        o.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(a.clone()),
            sup: CE::DataSomeValuesFrom {
                dp: DataProperty(dp.0.clone()),
                dr: exists_range,
            },
        }));
        o.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(a.clone()),
            sup: CE::DataAllValuesFrom {
                dp: DataProperty(dp.0.clone()),
                dr: le_minus_one.clone(),
            },
        }));
        o.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(a.clone()),
            i: Individual::Named(ind.clone()),
        }));
        o
    };

    // ∃p.nonNegativeInteger ⊓ ∀p.(integer[<= -1]): empty conjunction -> inconsistent.
    assert!(!is_ontology_consistent(&build_onto(DataRange::Datatype(nonneg.clone()))).unwrap());
    // Control: ∃p.integer ⊓ ∀p.(integer[<= -1]) is satisfiable (e.g. -1).
    assert!(is_ontology_consistent(&build_onto(DataRange::Datatype(integer.clone()))).unwrap());
}

#[test]
fn datetime_mixed_timezone_bound() {
    // Regression: a timezone-less value compared against a timezoned bound must
    // apply the maximum timezone correction (±14h), not be treated as trivially
    // satisfied.
    use horned_owl::model::{
        DataProperty, DataPropertyAssertion, DataPropertyRange, DataRange, FacetRestriction,
        Literal,
    };
    use horned_owl::vocab::Facet;
    use hermit_rs::reasoner::is_ontology_consistent;
    let build = Build::new_arc();
    let dp = build.data_property("http://example.org/when");
    let a = build.named_individual("http://example.org/a");
    let datetime = build.datatype("http://www.w3.org/2001/XMLSchema#dateTime");

    let range = || {
        DataRange::DatatypeRestriction(
            datetime.clone(),
            vec![FacetRestriction {
                f: Facet::MinInclusive,
                l: Literal::Datatype {
                    literal: "2025-01-01T00:00:00Z".to_string(),
                    datatype_iri: datetime.0.clone(),
                },
            }],
        )
    };
    let onto = |value: &str| {
        let mut o: SetOntology<_> = SetOntology::new();
        o.insert(Component::DataPropertyRange(DataPropertyRange {
            dp: DataProperty(dp.0.clone()),
            dr: range(),
        }));
        o.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
            dp: DataProperty(dp.0.clone()),
            from: Individual::Named(a.clone()),
            to: Literal::Datatype {
                literal: value.to_string(),
                datatype_iri: datetime.0.clone(),
            },
        }));
        o
    };

    // A timezone-less value well before bound+14h violates the timezoned minInclusive.
    assert!(!is_ontology_consistent(&onto("2020-01-01T00:00:00")).unwrap());
    // A timezone-less value well after the bound satisfies it.
    assert!(is_ontology_consistent(&onto("2030-01-01T00:00:00")).unwrap());
}

/// Regression: a functional data property relating one individual to two
/// distinct constants must be inconsistent. Each constant node carries a
/// singleton `ConstantEnumeration`; the functional merge copies both onto the
/// survivor, whose `{1} ⊓ {2}` datatype conjunction is empty (a clash). The
/// functional merge must preserve both constants' singleton enumerations, not
/// only the survivor's cached `constant_value`.
#[test]
fn functional_data_property_with_distinct_constants_is_inconsistent() {
    use horned_owl::model::{
        DataProperty, DataPropertyAssertion, FunctionalDataProperty, Literal,
    };
    let build = Build::new_arc();
    let dp = build.data_property("http://example.org/p");
    let a = build.named_individual("http://example.org/a");
    let integer = build.datatype("http://www.w3.org/2001/XMLSchema#integer");
    let lit = |v: &str| Literal::Datatype {
        literal: v.to_string(),
        datatype_iri: integer.0.clone(),
    };

    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::FunctionalDataProperty(FunctionalDataProperty(
        DataProperty(dp.0.clone()),
    )));
    ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: lit("1"),
    }));
    ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: DataProperty(dp.0.clone()),
        from: Individual::Named(a.clone()),
        to: lit("2"),
    }));
    assert!(!Reasoner::new(&clausify(&ontology)).is_consistent());

    // The same individual related twice to the SAME value is consistent.
    let mut ok: SetOntology<_> = SetOntology::new();
    ok.insert(Component::FunctionalDataProperty(FunctionalDataProperty(
        DataProperty(dp.0.clone()),
    )));
    for _ in 0..2 {
        ok.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
            dp: DataProperty(dp.0.clone()),
            from: Individual::Named(a.clone()),
            to: lit("1"),
        }));
    }
    assert!(Reasoner::new(&clausify(&ok)).is_consistent());
}

/// Regression: query reductions must use fresh witnesses that cannot collide
/// with user IRIs. The old code used a fixed `internal:test-individual`; an
/// ontology asserting `¬A(internal:test-individual)` then made A wrongly
/// unsatisfiable. With per-query fresh witnesses, A stays satisfiable.
#[test]
fn fresh_query_witness_does_not_collide_with_user_iri() {
    use hermit_rs::reasoner::is_concept_satisfiable;
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    // The exact IRI the old implementation used as its witness.
    let collider = build.named_individual("internal:test-individual");

    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(CE::Class(a.clone()))),
        i: Individual::Named(collider),
    }));
    // A is plainly satisfiable; the witness must not be identified with the
    // individual the ontology says is ¬A.
    assert!(is_concept_satisfiable(&ontology, CE::Class(a)).unwrap());
}

/// Regression: a single-atom `AnnotatedEquality` (the `<= 1 Inv(r)` / functional
/// case) whose two merge candidates are tree nodes at incompatible positions and
/// whose owner is a nominal must fire the nominal-introduction (NI) rule, not a
/// raw merge. A direct merge of the two tree nodes would panic in
/// `choose_merge_direction` ("unsupported merge type"); HermiT routes every
/// annotated equality through `NominalIntroductionManager`, which introduces a
/// fresh NI root, so the correct answer here is simply *consistent* (and, above
/// all, no panic).
#[test]
fn at_most_one_over_nominal_fires_ni_rule_not_raw_merge() {
    use horned_owl::model::{ObjectPropertyExpression, SubClassOf};

    let build = Build::new_arc();
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let a = build.class("http://example.org/A");
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let t = build.object_property("http://example.org/t");
    let u = build.object_property("http://example.org/u");
    let o = build.named_individual("http://example.org/o");
    let x = build.named_individual("http://example.org/x");

    let s_e = ObjectPropertyExpression::ObjectProperty(s.clone());
    let t_e = ObjectPropertyExpression::ObjectProperty(t.clone());
    let u_e = ObjectPropertyExpression::ObjectProperty(u.clone());
    let inv_r = ObjectPropertyExpression::InverseObjectProperty(r.clone());

    let mut ontology: SetOntology<_> = SetOntology::new();
    // C ⊑ ∃s.D, D ⊑ ∃t.A, C ⊑ ∃u.A  -> two A tree-nodes at different depths.
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(c.clone()),
        sup: CE::ObjectSomeValuesFrom { ope: s_e, bce: Box::new(CE::Class(d.clone())) },
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(d.clone()),
        sup: CE::ObjectSomeValuesFrom { ope: t_e, bce: Box::new(CE::Class(a.clone())) },
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(c.clone()),
        sup: CE::ObjectSomeValuesFrom { ope: u_e, bce: Box::new(CE::Class(a.clone())) },
    }));
    // A ⊑ ∃r.{o}: both A-nodes get an r-edge to the nominal o.
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectHasValue { ope: ObjectPropertyExpression::ObjectProperty(r.clone()), i: Individual::Named(o.clone()) },
    }));
    // o has at most one r-predecessor (≤1 Inv(r).⊤) -> the two A-nodes must be
    // identified; since they are tree nodes under a nominal, the NI rule fires.
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectMaxCardinality {
            n: 1,
            ope: inv_r,
            bce: Box::new(CE::Class(build.class("http://www.w3.org/2002/07/owl#Thing"))),
        },
        i: Individual::Named(o.clone()),
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(c.clone()),
        i: Individual::Named(x.clone()),
    }));

    // Must not panic, and the ontology is consistent.
    assert!(Reasoner::new(&clausify(&ontology)).is_consistent());
}

#[test]
fn instances_of_inconsistent_ontology_returns_all_individuals_even_direct() {
    // Java `getInstances` funnels through checkPreConditions() and THROWS
    // under the default flag. With the throw flag OFF the degenerate fallthrough
    // returns ALL named individuals for ANY class (everything is an instance of
    // everything), including the `direct=true` case — the path exercised here.
    // (The direct path uses this fallthrough, not `realize`, which would map
    // every individual to {owl:Nothing} and return empty for any class != owl:Nothing.)
    use hermit_rs::configuration::Configuration;
    use hermit_rs::reasoner::{instances, instances_with_configuration, INCONSISTENT_ONTOLOGY_ERROR};

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let ind = build.named_individual("http://example.org/a");

    // DisjointClasses(A,B) with A(a) and B(a) -> inconsistent.
    let mut onto: SetOntology<_> = SetOntology::new();
    onto.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(b.clone()),
        i: Individual::Named(ind.clone()),
    }));

    // Default flag: throws.
    assert_eq!(instances(&onto, &c, true).unwrap_err(), INCONSISTENT_ONTOLOGY_ERROR);

    // Flag OFF: degenerate return of all individuals, even direct=true.
    let mut cfg = Configuration::default();
    cfg.throw_inconsistent_ontology_exception = false;
    // C is unrelated to A/B and != owl:Nothing.
    let direct = instances_with_configuration(&onto, &c, true, &cfg).unwrap();
    assert!(direct.contains(&ind), "direct instances of C on an inconsistent ontology must include a");
    let non_direct = instances_with_configuration(&onto, &c, false, &cfg).unwrap();
    assert!(non_direct.contains(&ind));
}

// a property that is BOTH symmetric AND non-simple (transitive) must
// have the symmetric language spliced into its automaton (Java
// `finalizeConstruction` / `findSymmetricProperties`). Otherwise `∀r.C`
// under-propagates and a clash is missed. Unlike the simpler
// `symmetric_transitive_role_propagates_universal` (one reverse hop), this
// requires symmetry AND transitivity to *compose* across a third node.
#[test]
fn symmetric_splice_composes_with_transitivity() {
    use horned_owl::model::{
        ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf, SymmetricObjectProperty,
        TransitiveObjectProperty,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let r = build.object_property("http://example.org/r");
    let ind_a = build.named_individual("http://example.org/a");
    let ind_b = build.named_individual("http://example.org/b");
    let ind_c = build.named_individual("http://example.org/c");
    let ope = ObjectPropertyExpression::ObjectProperty(r.clone());

    // Symmetric(r), Transitive(r), A ⊑ ∀r.C, Disjoint(C,D), A(a), r(a,b),
    // r(c,b), D(c).
    //   r(c,b) + symmetry  ⟹ r(b,c)
    //   r(a,b) + r(b,c) + transitivity ⟹ r(a,c)
    //   ∀r.C on a ⟹ C(c); but D(c) and Disjoint(C,D) ⟹ inconsistent.
    // The reverse edge r(c,b) is only usable because r is symmetric, and the
    // composition is only possible because r is transitive: this needs the
    // symmetric language spliced into r's (non-simple) automaton.
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::SymmetricObjectProperty(SymmetricObjectProperty(ope.clone())));
    base.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(ope.clone())));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: ope.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind_a.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(ind_a.clone()),
        to: Individual::Named(ind_b.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(ind_c.clone()),
        to: Individual::Named(ind_b.clone()),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(ind_c.clone()),
    }));

    assert!(!is_ontology_consistent(&base).unwrap());

    // Drop D(c): now consistent (C(c) is fine).
    let mut without_d = base.clone();
    let d_c: horned_owl::model::AnnotatedComponent<_> = Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(ind_c.clone()),
    })
    .into();
    without_d.take(&d_c);
    assert!(is_ontology_consistent(&without_d).unwrap());
}

// An ontology with equivalent properties a≡b plus cross-chains
// a∘x⊑b, b∘y⊑a has a cycle a→b→a in the dependency graph that HermiT trims
// via the equivalent-property loop in `checkForRegularity`; it must be
// accepted (not rejected as "not regular").
#[test]
fn equivalent_properties_with_cross_chains_is_regular() {
    use horned_owl::model::{
        EquivalentObjectProperties, ObjectPropertyExpression, SubObjectPropertyExpression,
        SubObjectPropertyOf,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.object_property("http://example.org/a");
    let b = build.object_property("http://example.org/b");
    let x = build.object_property("http://example.org/x");
    let y = build.object_property("http://example.org/y");
    let a_e = ObjectPropertyExpression::ObjectProperty(a.clone());
    let b_e = ObjectPropertyExpression::ObjectProperty(b.clone());
    let x_e = ObjectPropertyExpression::ObjectProperty(x.clone());
    let y_e = ObjectPropertyExpression::ObjectProperty(y.clone());

    // a ≡ b, a∘x ⊑ b, b∘y ⊑ a.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::EquivalentObjectProperties(EquivalentObjectProperties(vec![
        a_e.clone(),
        b_e.clone(),
    ])));
    ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![a_e.clone(), x_e.clone()]),
        sup: b_e.clone(),
    }));
    ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![b_e.clone(), y_e.clone()]),
        sup: a_e.clone(),
    }));

    // HermiT accepts this (the a→b→a cycle is trimmed); the reasoner must build
    // the automata without raising a "not regular" error and report consistent.
    assert!(is_ontology_consistent(&ontology).unwrap());
}

// `∀r.C` over a property `r` whose declared inverse `s` is *complex*
// (transitive). `connectAllAutomata`'s inverse-union pass must enrich r's
// automaton with the mirror of s's automaton so the universal propagates
// along the inverse of the complex role.
#[test]
fn universal_propagates_along_inverse_of_complex_role() {
    use horned_owl::model::{
        InverseObjectProperties, ObjectPropertyAssertion, ObjectPropertyExpression, SubClassOf,
        TransitiveObjectProperty,
    };
    use hermit_rs::reasoner::is_ontology_consistent;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let ind_a = build.named_individual("http://example.org/a");
    let ind_b = build.named_individual("http://example.org/b");
    let ind_c = build.named_individual("http://example.org/c");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let s_e = ObjectPropertyExpression::ObjectProperty(s.clone());

    // InverseObjectProperties(r, s) [so r ≡ Inv(s)], Transitive(s),
    // A ⊑ ∀r.C, Disjoint(C,D), A(a), s(b,a), s(c,b), D(c).
    //   Transitive(s): s(b,a)+s(c,b) ⟹ s(c,a)  (so s(c,a), s(b,a) hold)
    //   r = Inv(s): r(a,b) and r(a,c) hold.
    //   ∀r.C on a ⟹ C(c); D(c)+Disjoint(C,D) ⟹ inconsistent.
    // r itself has no chain, so r's automaton is trivial unless enriched with
    // the mirror of its complex inverse s's automaton.
    let mut base: SetOntology<_> = SetOntology::new();
    base.insert(Component::InverseObjectProperties(InverseObjectProperties(
        r.clone(),
        s.clone(),
    )));
    base.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(s_e.clone())));
    base.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectAllValuesFrom { ope: r_e.clone(), bce: Box::new(CE::Class(c.clone())) },
    }));
    base.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind_a.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: s_e.clone(),
        from: Individual::Named(ind_b.clone()),
        to: Individual::Named(ind_a.clone()),
    }));
    base.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: s_e.clone(),
        from: Individual::Named(ind_c.clone()),
        to: Individual::Named(ind_b.clone()),
    }));
    base.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(ind_c.clone()),
    }));

    assert!(!is_ontology_consistent(&base).unwrap());

    // Drop D(c): now consistent.
    let mut without_d = base.clone();
    let d_c: horned_owl::model::AnnotatedComponent<_> = Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(d.clone()),
        i: Individual::Named(ind_c.clone()),
    })
    .into();
    without_d.take(&d_c);
    assert!(is_ontology_consistent(&without_d).unwrap());
}

#[test]
fn disjoint_classes_with_duplicate_operand_is_not_overconstrained() {
    // HermiT iterates DisjointClasses operands as a Set, so a repeated
    // operand is collapsed. DisjointClasses(C C D) must NOT entail C ⊑ ⊥; an
    // instance of C stays consistent. Before the dedup fix the port formed the
    // pair {¬C, ¬C} = C ⊑ ⊥ and reported inconsistent.
    let build = Build::new_arc();
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");
    let a = build.named_individual("http://example.org/a");

    let mut onto: SetOntology<_> = SetOntology::new();
    onto.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(c.clone()),
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(c.clone()),
        i: Individual::Named(a.clone()),
    }));

    assert!(Reasoner::new(&clausify(&onto)).is_consistent());
}

// A CountingMonitor attached to a real consistency run observes the core
// lifecycle events (node creations and iterations). This proves the monitor is
// actually wired into the tableau (the events fire), and is answer-neutral --
// the consistency result is identical with and without the monitor.
#[test]
fn counting_monitor_observes_a_real_run() {
    use horned_owl::model::SubClassOf;
    use hermit_rs::monitor::CountingMonitor;

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let r = build.object_property("http://example.org/r");
    let ind = build.named_individual("http://example.org/x");

    // A ⊑ ∃r.B, with A(x): forces an existential expansion (a fresh successor
    // node) during the run, so the monitor must see >0 node creations and >0
    // iterations.
    let mut onto: SetOntology<_> = SetOntology::new();
    onto.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectSomeValuesFrom {
            ope: horned_owl::model::ObjectPropertyExpression::ObjectProperty(r.clone()),
            bce: Box::new(CE::Class(b.clone())),
        },
    }));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));

    let dl_ontology = clausify(&onto);
    let reasoner = Reasoner::new(&dl_ontology);

    // Reference result (no monitor) and monitored result must agree.
    let plain = reasoner.is_consistent();
    let (monitored, counts) = reasoner.is_consistent_with_monitor(CountingMonitor::new());
    assert_eq!(plain, monitored);
    assert!(monitored, "the ontology is consistent");

    // The monitor observed the run: nodes were created and iterations ran.
    assert!(
        counts.number_of_nodes > 0,
        "monitor should have observed node creations, got {}",
        counts.number_of_nodes
    );
    assert!(
        counts.number_of_iterations > 0,
        "monitor should have observed iterations, got {}",
        counts.number_of_iterations
    );
    assert_eq!(counts.last_result, Some(true));
}

/// Clausifies and reasons with `ignoreUnsupportedDatatypes` enabled (the
/// non-default mode in which an unsupported datatype `D` is tolerated and treated
/// as a fresh infinite value space whose `D`/`¬D` value spaces must stay
/// disjoint). Returns whether the ontology is consistent.
fn is_consistent_ignoring_unsupported(ontology: &SetOntology<hermit_rs::structural::A>) -> bool {
    // The clausifier and the reasoner carry distinct configuration structs; set
    // the ignore-unsupported flag on both (so the datatype is tolerated AND the
    // unknown-datatype tableau phase activates).
    let mut clausify_config = Configuration::default();
    clausify_config.ignore_unsupported_datatypes = true;
    let mut reasoner_config = hermit_rs::configuration::Configuration::default();
    reasoner_config.ignore_unsupported_datatypes = true;
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology).unwrap();
    let axioms = normalization.into_axioms();
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    let dl_ontology = OWLClausification::new(clausify_config)
        .clausify("http://example.org/onto", &axioms, &expressivity)
        .unwrap();
    Reasoner::with_configuration(&dl_ontology, reasoner_config).is_consistent()
}

/// Regression for `applyUnknownDatatypeRestrictionSemantics` /
/// `generateInequalitiesFor` (DatatypeManager.java:102-141), wired into
/// `doIteration` ahead of `checkDatatypeConstraints` and gated on
/// `ignoreUnsupportedDatatypes`.
///
/// An unsupported datatype `D` is modelled as a fresh infinite value space: a
/// node in `D` and a node in `¬D` must be kept apart. Forcing one functional data
/// successor to be in both `D` and `¬D` is therefore unsatisfiable -- but ONLY
/// via this phase, since the conjunction checker soundly declines to judge the
/// unknown datatype `D` (so `D ⊓ ¬D` on one node is not otherwise a clash).
#[test]
fn unknown_datatype_restriction_inequality_semantics() {
    use horned_owl::model::{
        ClassAssertion, DataProperty, DataRange, FunctionalDataProperty, SubClassOf,
    };
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let v = build.data_property("http://example.org/v");
    let ind = build.named_individual("http://example.org/a");
    // An unsupported (custom, undeclared) datatype: under ignoreUnsupportedDatatypes
    // it joins the unknown-restriction set and becomes a fresh value space.
    let unknown = build.datatype("http://example.org/UnknownDatatype");

    let d = DataRange::Datatype(unknown.clone());
    let not_d = DataRange::DataComplementOf(Box::new(DataRange::Datatype(unknown.clone())));

    // Functional(v), A ⊑ ∃v.D, A ⊑ ∃v.¬D, A(a): the single v-successor must lie in
    // both D and ¬D. The unknown-datatype phase keeps D and ¬D apart, so this is
    // inconsistent (and is only detected by that phase).
    let mut conflict: SetOntology<_> = SetOntology::new();
    conflict.insert(Component::FunctionalDataProperty(FunctionalDataProperty(DataProperty(
        v.0.clone(),
    ))));
    conflict.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::DataSomeValuesFrom { dp: DataProperty(v.0.clone()), dr: d.clone() },
    }));
    conflict.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::DataSomeValuesFrom { dp: DataProperty(v.0.clone()), dr: not_d },
    }));
    conflict.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));
    assert!(
        !is_consistent_ignoring_unsupported(&conflict),
        "D and not-D on one functional successor must clash via the unknown-datatype phase"
    );

    // Control: only ∃v.D (no ¬D). The unknown datatype is a non-empty fresh value
    // space, so this is satisfiable -- confirming the phase does not over-clash.
    let mut ok: SetOntology<_> = SetOntology::new();
    ok.insert(Component::FunctionalDataProperty(FunctionalDataProperty(DataProperty(
        v.0.clone(),
    ))));
    ok.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::DataSomeValuesFrom { dp: DataProperty(v.0.clone()), dr: d },
    }));
    ok.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));
    assert!(
        is_consistent_ignoring_unsupported(&ok),
        "a single unknown-datatype successor is satisfiable (fresh infinite value space)"
    );
}
