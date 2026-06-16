// Tests for the structural foundation (OWLAxioms container, expressivity
// analysis, built-in property axiomatization).

use horned_owl::model::{
    Build, ClassExpression as CE, Individual, ObjectPropertyExpression,
};

use hermit_rs::structural::{
    BuiltInPropertyManager, ExpressionManager, OWLAxiomsExpressivity, OWLAxioms,
};

#[test]
fn expressivity_detects_at_most_inverse_and_nominals() {
    let build = Build::new_arc();
    let r = build.object_property("http://example.org/r");
    let a = build.class("http://example.org/A");
    let i = build.named_individual("http://example.org/i");

    let mut axioms = OWLAxioms::new();
    // ObjectMaxCardinality(1 inv(r) A) -> at-most + inverse role.
    axioms.concept_inclusions.push(vec![CE::ObjectMaxCardinality {
        n: 1,
        ope: ObjectPropertyExpression::InverseObjectProperty(r.clone()),
        bce: Box::new(CE::Class(a.clone())),
    }]);
    // ObjectOneOf(i) -> nominals.
    axioms
        .concept_inclusions
        .push(vec![CE::ObjectOneOf(vec![Individual::Named(i)])]);

    let e = OWLAxiomsExpressivity::new(&axioms);
    assert!(e.has_at_most_restrictions);
    assert!(e.has_inverse_roles);
    assert!(e.has_nominals);
    assert!(!e.has_datatypes);
    assert!(!e.has_swrl_rules);
}

#[test]
fn built_in_top_object_property_axiomatized_only_when_used() {
    let build = Build::new_arc();

    // An ontology that does not mention owl:topObjectProperty: nothing added.
    let mut unused = OWLAxioms::new();
    let r = build.object_property("http://example.org/r");
    unused.simple_object_property_inclusions.push([
        ObjectPropertyExpression::ObjectProperty(r.clone()),
        ObjectPropertyExpression::ObjectProperty(r.clone()),
    ]);
    let manager = BuiltInPropertyManager::new();
    let before = unused.concept_inclusions.len();
    manager.axiomatize_built_in_properties_as_needed(&mut unused);
    assert_eq!(unused.concept_inclusions.len(), before);

    // An ontology that uses owl:topObjectProperty: the three top-property
    // axioms are added (transitive, symmetric, and the Thing inclusion).
    let mut used = OWLAxioms::new();
    let top = build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty");
    used.simple_object_property_inclusions.push([
        ObjectPropertyExpression::ObjectProperty(top.clone()),
        ObjectPropertyExpression::ObjectProperty(r),
    ]);
    manager.axiomatize_built_in_properties_as_needed(&mut used);
    assert_eq!(used.concept_inclusions.len(), 1);
    assert_eq!(used.complex_object_property_inclusions.len(), 1);
    // The original inclusion plus the new symmetric one.
    assert_eq!(used.simple_object_property_inclusions.len(), 2);
}

#[test]
fn complement_nnf_pushes_negation_inward() {
    let build = Build::new_arc();
    let em = ExpressionManager::new();
    let r = build.object_property("http://example.org/r");
    let a = build.class("http://example.org/A");

    // NNF of not(exists r.A) is forall r.(not A).
    let some = CE::ObjectSomeValuesFrom {
        ope: ObjectPropertyExpression::ObjectProperty(r.clone()),
        bce: Box::new(CE::Class(a.clone())),
    };
    let complement = CE::ObjectComplementOf(Box::new(some));
    let nnf = em.get_nnf(&complement);
    match nnf {
        CE::ObjectAllValuesFrom { bce, .. } => match *bce {
            CE::ObjectComplementOf(inner) => assert_eq!(*inner, CE::Class(a)),
            other => panic!("expected complement filler, got {other:?}"),
        },
        other => panic!("expected forall, got {other:?}"),
    }
}

#[test]
fn simplify_collapses_double_negation_and_thing() {
    let build = Build::new_arc();
    let em = ExpressionManager::new();
    let a = build.class("http://example.org/A");
    let thing = build.class("http://www.w3.org/2002/07/owl#Thing");

    // not(not A) simplifies to A.
    let double_neg =
        CE::ObjectComplementOf(Box::new(CE::ObjectComplementOf(Box::new(CE::Class(a.clone())))));
    assert_eq!(em.get_simplified(&double_neg), CE::Class(a.clone()));

    // A intersect Thing simplifies to A (Thing conjunct dropped, single
    // remaining conjunct kept inside the intersection).
    let inter = CE::ObjectIntersectionOf(vec![CE::Class(a.clone()), CE::Class(thing)]);
    match em.get_simplified(&inter) {
        CE::ObjectIntersectionOf(operands) => assert_eq!(operands, vec![CE::Class(a)]),
        other => panic!("expected intersection, got {other:?}"),
    }
}

#[test]
fn normalization_produces_concept_inclusions() {
    use horned_owl::model::{Component, MutableOntology, SubClassOf};
    use horned_owl::ontology::set::SetOntology;
    use hermit_rs::structural::{OWLAxioms, OWLNormalization};

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");

    // SubClassOf(A, B): A ⊑ B.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    }));

    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(&ontology).unwrap();
    let axioms = normalization.into_axioms();

    // One concept inclusion {not A, B} is produced (Thing ⊑ ¬A ⊔ B).
    assert_eq!(axioms.concept_inclusions.len(), 1);
    let inclusion = &axioms.concept_inclusions[0];
    assert_eq!(inclusion.len(), 2);
    assert!(inclusion.contains(&CE::ObjectComplementOf(Box::new(CE::Class(a)))));
    assert!(inclusion.contains(&CE::Class(b)));
}

#[test]
fn normalization_accepts_swrl_rules() {
    use horned_owl::model::{Atom, Build, Component, IArgument, MutableOntology, Rule};
    use horned_owl::ontology::set::SetOntology;
    use hermit_rs::structural::{OWLAxioms, OWLNormalization};

    // SWRL rules are now normalized by RuleNormalizer (body→head pairs) rather
    // than rejected. A rule with a non-empty body becomes one DisjunctiveRule per
    // head atom; an empty-body rule is instead turned into facts
    // (Rule2FactConverter), so it does NOT contribute to `rules`.
    let build = Build::new_arc();
    let c = build.class("http://example.com/C");
    let d = build.class("http://example.com/D");
    let x = IArgument::Variable(build.variable("urn:swrl#x"));
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::Rule(Rule {
        body: vec![Atom::ClassAtom { pred: c.into(), arg: x.clone() }],
        head: vec![Atom::ClassAtom { pred: d.into(), arg: x }],
    }));
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    assert!(normalization.process_ontology(&ontology).is_ok());
    assert_eq!(normalization.axioms().rules.len(), 1);
}

#[test]
fn end_to_end_clausification_subclass() {
    use horned_owl::model::{Component, MutableOntology, SubClassOf};
    use horned_owl::ontology::set::SetOntology;
    use hermit_rs::structural::{
        Configuration, OWLAxioms, OWLAxiomsExpressivity, OWLClausification, OWLNormalization,
    };

    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");

    // A ⊑ B, with A and B declared.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::DeclareClass(horned_owl::model::DeclareClass(a.clone())));
    ontology.insert(Component::DeclareClass(horned_owl::model::DeclareClass(b.clone())));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    }));

    // Normalize.
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(&ontology).unwrap();
    let axioms = normalization.into_axioms();
    let expressivity = OWLAxiomsExpressivity::new(&axioms);

    // Clausify.
    let clausifier = OWLClausification::new(Configuration::default());
    let dl_ontology = clausifier
        .clausify("http://example.org/onto", &axioms, &expressivity)
        .unwrap();

    // Both atomic concepts are in the vocabulary.
    assert!(dl_ontology.contains_atomic_concept(&hermit_rs::model::AtomicConcept::create(
        "http://example.org/A"
    )));
    assert!(dl_ontology.contains_atomic_concept(&hermit_rs::model::AtomicConcept::create(
        "http://example.org/B"
    )));
    // The clausified ontology has exactly one DL clause: B(X) :- A(X).
    assert_eq!(dl_ontology.get_dl_clauses().len(), 1);
    let clause = dl_ontology.get_dl_clauses().iter().next().unwrap();
    assert!(clause.is_atomic_concept_inclusion());
    assert!(dl_ontology.is_horn());
}

#[test]
fn top_data_property_in_data_restriction_is_rejected_not_panicked() {
    // HermiT's checkTopDataPropertyUse throws IllegalArgumentException for
    // owl:topDataProperty anywhere but the super-property position of
    // SubDataPropertyOf. The port must return a clean Err (not panic).
    use horned_owl::model::{ClassAssertion, Component, Individual, MutableOntology};
    use horned_owl::ontology::set::SetOntology;
    use hermit_rs::structural::{OWLAxioms, OWLNormalization};

    let build = Build::new_arc();
    let top_dp = build.data_property("http://www.w3.org/2002/07/owl#topDataProperty");
    let xsd_integer = build.datatype("http://www.w3.org/2001/XMLSchema#integer");
    let a = build.named_individual("http://example.org/a");

    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::DataAllValuesFrom {
            dp: top_dp,
            dr: horned_owl::model::DataRange::Datatype(xsd_integer),
        },
        i: Individual::Named(a),
    }));

    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    let result = normalization.process_ontology(&ontology);
    assert!(result.is_err(), "owl:topDataProperty in a data restriction must be rejected with Err, not panic");
}
