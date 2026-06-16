// Regression tests for the entailment / realization parity work:
//  - declaration/annotation/import axioms entail `true`
//  - get_types(individual, direct) incl. owl:Thing and the fresh case
//  - object-property characteristics entailment
//  - data-property assertions
//  - FunctionalDataProperty
//  - HasKey
//  - SubPropertyChainOf
//
// Each mirrors the corresponding Java reduction in EntailmentChecker /
// Reasoner; see comments in src/reasoner.rs.

use horned_owl::model::{
    AsymmetricObjectProperty, Build, Class, ClassAssertion, ClassExpression as CE, Component,
    DataPropertyAssertion, DeclareClass, FunctionalDataProperty, HasKey, Individual, Literal,
    MutableOntology, NamedIndividual, NegativeDataPropertyAssertion, ObjectProperty,
    ObjectPropertyExpression as OPE, PropertyExpression,
    ReflexiveObjectProperty, SubClassOf, SubObjectPropertyOf, SubObjectPropertyExpression,
    TransitiveObjectProperty,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner::{get_types, is_entailed};

type O = SetOntology<hermit_rs::structural::A>;

fn cls(b: &Build<std::sync::Arc<str>>, n: &str) -> Class<hermit_rs::structural::A> {
    b.class(format!("http://example.org/{n}"))
}
fn op(b: &Build<std::sync::Arc<str>>, n: &str) -> ObjectProperty<hermit_rs::structural::A> {
    b.object_property(format!("http://example.org/{n}"))
}
fn ind(b: &Build<std::sync::Arc<str>>, n: &str) -> NamedIndividual<hermit_rs::structural::A> {
    b.named_individual(format!("http://example.org/{n}"))
}

// ----------------------------------------------------------------------------
// declaration / annotation / import axioms are vacuously entailed.
// EntailmentChecker.visit(OWLDeclarationAxiom) returns Boolean.TRUE.
// ----------------------------------------------------------------------------

#[test]
fn declaration_axiom_is_entailed() {
    let b = Build::new_arc();
    let onto: O = SetOntology::new();
    let decl = Component::DeclareClass(DeclareClass(cls(&b, "A")));
    assert!(is_entailed(&onto, &decl).unwrap());
}

#[test]
fn annotation_assertion_is_entailed() {
    use horned_owl::model::{Annotation, AnnotationAssertion, AnnotationSubject, AnnotationValue};
    let b = Build::new_arc();
    let onto: O = SetOntology::new();
    let ann = Component::AnnotationAssertion(AnnotationAssertion {
        subject: AnnotationSubject::IRI(b.iri("http://example.org/A")),
        ann: Annotation {
            ap: b.annotation_property("http://example.org/p"),
            av: AnnotationValue::Literal(Literal::Simple { literal: "x".into() }),
        },
    });
    assert!(is_entailed(&onto, &ann).unwrap());
}

#[test]
fn import_declaration_is_entailed() {
    let b = Build::new_arc();
    let onto: O = SetOntology::new();
    let imp = Component::Import(horned_owl::model::Import(b.iri("http://example.org/other")));
    assert!(is_entailed(&onto, &imp).unwrap());
}

// ----------------------------------------------------------------------------
// get_types(individual, direct).
// Reasoner.getTypes (Reasoner.java:1620).
// ----------------------------------------------------------------------------

#[test]
fn get_types_indirect_includes_thing_and_ancestors() {
    let b = Build::new_arc();
    let thing = b.class("http://www.w3.org/2002/07/owl#Thing");
    let mut onto: O = SetOntology::new();
    // A ⊑ B, a : A.  Types(a, false) = {A, B, owl:Thing}.
    onto.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(cls(&b, "A")),
        sup: CE::Class(cls(&b, "B")),
    }));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(cls(&b, "A")),
        i: Individual::Named(ind(&b, "a")),
    }));

    let types = get_types(&onto, &ind(&b, "a"), false).unwrap();
    assert!(types.contains(&cls(&b, "A")), "A in {types:?}");
    assert!(types.contains(&cls(&b, "B")), "B in {types:?}");
    assert!(types.contains(&thing), "owl:Thing in {types:?}");

    // Direct types: only A (the most specific).
    let direct = get_types(&onto, &ind(&b, "a"), true).unwrap();
    assert!(direct.contains(&cls(&b, "A")));
    assert!(!direct.contains(&cls(&b, "B")));
    assert!(!direct.contains(&thing));
}

#[test]
fn get_types_undefined_individual_is_thing() {
    let b = Build::new_arc();
    let thing = b.class("http://www.w3.org/2002/07/owl#Thing");
    let mut onto: O = SetOntology::new();
    onto.insert(Component::DeclareClass(DeclareClass(cls(&b, "A"))));
    // `ghost` does not occur anywhere -> isDefined false -> {owl:Thing}.
    let types = get_types(&onto, &ind(&b, "ghost"), false).unwrap();
    assert_eq!(types, std::iter::once(thing).collect());
}

// ----------------------------------------------------------------------------
// object-property characteristics entailment.
// ----------------------------------------------------------------------------

#[test]
fn transitive_object_property_entailment() {
    let b = Build::new_arc();
    let r = op(&b, "r");
    // r ∘ r ⊑ r makes r transitive.
    let mut onto: O = SetOntology::new();
    onto.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![
            OPE::ObjectProperty(r.clone()),
            OPE::ObjectProperty(r.clone()),
        ]),
        sup: OPE::ObjectProperty(r.clone()),
    }));
    let ax = Component::TransitiveObjectProperty(TransitiveObjectProperty(OPE::ObjectProperty(
        r.clone(),
    )));
    assert!(is_entailed(&onto, &ax).unwrap());

    // Without the chain axiom, transitivity is not entailed.
    let empty: O = SetOntology::new();
    assert!(!is_entailed(&empty, &ax).unwrap());
}

#[test]
fn reflexive_object_property_entailment() {
    let b = Build::new_arc();
    let r = op(&b, "r");
    // ⊤ ⊑ ∃r.Self-ish: assert ⊤ ⊑ ∃r.⊤ won't make reflexive; use explicit reflexive.
    let mut onto: O = SetOntology::new();
    onto.insert(Component::ReflexiveObjectProperty(ReflexiveObjectProperty(
        OPE::ObjectProperty(r.clone()),
    )));
    let ax = Component::ReflexiveObjectProperty(ReflexiveObjectProperty(OPE::ObjectProperty(
        r.clone(),
    )));
    assert!(is_entailed(&onto, &ax).unwrap());

    let empty: O = SetOntology::new();
    assert!(!is_entailed(&empty, &ax).unwrap());
}

#[test]
fn asymmetric_and_irreflexive_object_property_entailment() {
    use horned_owl::model::IrreflexiveObjectProperty;
    let b = Build::new_arc();
    let r = op(&b, "r");
    let mut onto: O = SetOntology::new();
    onto.insert(Component::AsymmetricObjectProperty(AsymmetricObjectProperty(
        OPE::ObjectProperty(r.clone()),
    )));
    onto.insert(Component::IrreflexiveObjectProperty(
        IrreflexiveObjectProperty(OPE::ObjectProperty(r.clone())),
    ));
    let asym = Component::AsymmetricObjectProperty(AsymmetricObjectProperty(OPE::ObjectProperty(
        r.clone(),
    )));
    let irr = Component::IrreflexiveObjectProperty(IrreflexiveObjectProperty(
        OPE::ObjectProperty(r.clone()),
    ));
    assert!(is_entailed(&onto, &asym).unwrap());
    assert!(is_entailed(&onto, &irr).unwrap());

    let empty: O = SetOntology::new();
    assert!(!is_entailed(&empty, &asym).unwrap());
    assert!(!is_entailed(&empty, &irr).unwrap());
}

// ----------------------------------------------------------------------------
// SubPropertyChainOf entailment.
// EntailmentChecker.visit(OWLSubPropertyChainOfAxiom).
// ----------------------------------------------------------------------------

#[test]
fn sub_property_chain_entailment() {
    let b = Build::new_arc();
    let r = op(&b, "r");
    let s = op(&b, "s");
    let t = op(&b, "t");
    // r ∘ s ⊑ t asserted -> entailed.
    let mut onto: O = SetOntology::new();
    onto.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![
            OPE::ObjectProperty(r.clone()),
            OPE::ObjectProperty(s.clone()),
        ]),
        sup: OPE::ObjectProperty(t.clone()),
    }));
    let ax = Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![
            OPE::ObjectProperty(r.clone()),
            OPE::ObjectProperty(s.clone()),
        ]),
        sup: OPE::ObjectProperty(t.clone()),
    });
    assert!(is_entailed(&onto, &ax).unwrap());

    let empty: O = SetOntology::new();
    assert!(!is_entailed(&empty, &ax).unwrap());
}

// ----------------------------------------------------------------------------
// data-property assertions.
// EntailmentChecker.visit(OWLDataPropertyAssertionAxiom).
// ----------------------------------------------------------------------------

fn lit_int(v: &str) -> Literal<hermit_rs::structural::A> {
    let b = Build::new_arc();
    Literal::Datatype {
        literal: v.into(),
        datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#integer"),
    }
}

#[test]
fn data_property_assertion_entailment() {
    let b = Build::new_arc();
    let dp = b.data_property("http://example.org/age");
    let mut onto: O = SetOntology::new();
    onto.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: dp.clone(),
        from: Individual::Named(ind(&b, "a")),
        to: lit_int("42"),
    }));
    let ax = Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: dp.clone(),
        from: Individual::Named(ind(&b, "a")),
        to: lit_int("42"),
    });
    assert!(is_entailed(&onto, &ax).unwrap());

    // A different value is not entailed.
    let other = Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: dp.clone(),
        from: Individual::Named(ind(&b, "a")),
        to: lit_int("43"),
    });
    assert!(!is_entailed(&onto, &other).unwrap());
}

#[test]
fn negative_data_property_assertion_entailment() {
    let b = Build::new_arc();
    let dp = b.data_property("http://example.org/age");
    // a age 42, and age functional => a does NOT have age 43.
    let mut onto: O = SetOntology::new();
    onto.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: dp.clone(),
        from: Individual::Named(ind(&b, "a")),
        to: lit_int("42"),
    }));
    onto.insert(Component::FunctionalDataProperty(FunctionalDataProperty(
        dp.clone(),
    )));
    let neg = Component::NegativeDataPropertyAssertion(NegativeDataPropertyAssertion {
        dp: dp.clone(),
        from: Individual::Named(ind(&b, "a")),
        to: lit_int("43"),
    });
    assert!(is_entailed(&onto, &neg).unwrap());
}

// ----------------------------------------------------------------------------
// FunctionalDataProperty.
// EntailmentChecker.visit(OWLFunctionalDataPropertyAxiom).
// ----------------------------------------------------------------------------

#[test]
fn functional_data_property_entailment() {
    let b = Build::new_arc();
    let thing = b.class("http://www.w3.org/2002/07/owl#Thing");
    let dp = b.data_property("http://example.org/age");
    // ⊤ ⊑ ≤1 age makes age functional.
    let mut onto: O = SetOntology::new();
    onto.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(thing.clone()),
        sup: CE::DataMaxCardinality {
            n: 1,
            dp: dp.clone(),
            dr: horned_owl::model::DataRange::Datatype(
                b.datatype("http://www.w3.org/2000/01/rdf-schema#Literal"),
            ),
        },
    }));
    let ax = Component::FunctionalDataProperty(FunctionalDataProperty(dp.clone()));
    assert!(is_entailed(&onto, &ax).unwrap());

    let empty: O = SetOntology::new();
    assert!(!is_entailed(&empty, &ax).unwrap());
}

// ----------------------------------------------------------------------------
// HasKey.
// EntailmentChecker.visit(OWLHasKeyAxiom).
// ----------------------------------------------------------------------------

#[test]
fn has_key_object_property_entailment() {
    let b = Build::new_arc();
    let person = cls(&b, "Person");
    let has_ssn = op(&b, "hasSSN");
    // HasKey(Person, hasSSN) combined with hasSSN being functional-inverse...
    // The key is entailed iff two Persons sharing a hasSSN successor must be equal.
    // Make hasSSN inverse-functional so the shared successor forces equality.
    use horned_owl::model::InverseFunctionalObjectProperty;
    let mut onto: O = SetOntology::new();
    onto.insert(Component::InverseFunctionalObjectProperty(
        InverseFunctionalObjectProperty(OPE::ObjectProperty(has_ssn.clone())),
    ));
    let key = Component::HasKey(HasKey {
        ce: CE::Class(person.clone()),
        vpe: vec![PropertyExpression::ObjectPropertyExpression(
            OPE::ObjectProperty(has_ssn.clone()),
        )],
    });
    assert!(is_entailed(&onto, &key).unwrap());
}

#[test]
fn has_key_not_entailed_without_constraint() {
    let b = Build::new_arc();
    let person = cls(&b, "Person");
    let has_ssn = op(&b, "hasSSN");
    let onto: O = SetOntology::new();
    let key = Component::HasKey(HasKey {
        ce: CE::Class(person.clone()),
        vpe: vec![PropertyExpression::ObjectPropertyExpression(
            OPE::ObjectProperty(has_ssn.clone()),
        )],
    });
    // No constraint => two Persons sharing a successor need not be equal.
    assert!(!is_entailed(&onto, &key).unwrap());
}

// ----------------------------------------------------------------------------
// An inconsistent ontology under HermiT's default configuration
// (throwInconsistentOntologyException = true). The public query methods that
// Java routes through `checkPreConditions` THROW (here: return the distinctive
// InconsistentOntology Err), while `getInstances`/`getTypes` reproduce HermiT's
// explicit RETURNING behaviour and do NOT throw.
// ----------------------------------------------------------------------------

fn inconsistent_ontology() -> (O, NamedIndividual<hermit_rs::structural::A>) {
    use horned_owl::model::DisjointClasses;
    let b = Build::new_arc();
    let a = cls(&b, "A");
    let bb = cls(&b, "B");
    let x = ind(&b, "x");
    let mut onto: O = SetOntology::new();
    // DisjointClasses(A, B), A(x), B(x)  ->  inconsistent.
    onto.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(bb.clone()),
    ])));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(x.clone()),
    }));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(bb.clone()),
        i: Individual::Named(x.clone()),
    }));
    (onto, x)
}

#[test]
fn check_precondition_methods_throw_on_inconsistent_ontology() {
    use hermit_rs::reasoner::{
        disjoint_classes, equivalent_classes, is_concept_satisfiable, is_entailed,
        is_instance_of, is_subsumed_by, sub_classes, super_classes, INCONSISTENT_ONTOLOGY_ERROR,
    };
    let b = Build::new_arc();
    let (onto, x) = inconsistent_ontology();
    let a = cls(&b, "A");
    let bb = cls(&b, "B");

    // Each must be the distinctive InconsistentOntology Err.
    macro_rules! assert_inconsistent_err {
        ($e:expr) => {{
            match $e {
                Err(msg) => assert_eq!(msg, INCONSISTENT_ONTOLOGY_ERROR),
                Ok(_) => panic!("expected InconsistentOntology Err, got Ok"),
            }
        }};
    }

    assert_inconsistent_err!(sub_classes(&onto, &a, false));
    assert_inconsistent_err!(super_classes(&onto, &a, false));
    assert_inconsistent_err!(equivalent_classes(&onto, &a));
    assert_inconsistent_err!(disjoint_classes(&onto, &a));
    assert_inconsistent_err!(is_concept_satisfiable(&onto, CE::Class(a.clone())));
    assert_inconsistent_err!(is_subsumed_by(
        &onto,
        CE::Class(a.clone()),
        CE::Class(bb.clone())
    ));
    assert_inconsistent_err!(is_instance_of(&onto, x.clone(), CE::Class(a.clone())));
    assert_inconsistent_err!(is_entailed(
        &onto,
        &Component::SubClassOf(SubClassOf {
            sub: CE::Class(a.clone()),
            sup: CE::Class(bb.clone()),
        })
    ));
}

#[test]
fn get_types_and_get_instances_throw_on_inconsistent_ontology_default_flag() {
    use hermit_rs::reasoner::{
        get_types, get_types_with_configuration, instances, instances_with_configuration,
        INCONSISTENT_ONTOLOGY_ERROR,
    };
    use hermit_rs::configuration::Configuration;
    let b = Build::new_arc();
    let (onto, x) = inconsistent_ontology();
    let a = cls(&b, "A");
    let nothing = b.class("http://www.w3.org/2002/07/owl#Nothing");

    // Java getTypes()/getInstances() funnel through checkPreConditions(),
    // which throws InconsistentOntologyException under the DEFAULT throw flag.
    let err = get_types(&onto, &x, true).unwrap_err();
    assert_eq!(err, INCONSISTENT_ONTOLOGY_ERROR);
    let err = instances(&onto, &a, false).unwrap_err();
    assert_eq!(err, INCONSISTENT_ONTOLOGY_ERROR);

    // Flag OFF: the degenerate "return" behaviour is the fallthrough — getTypes
    // collapses to {owl:Nothing}; getInstances returns all named individuals.
    let mut cfg = Configuration::default();
    cfg.throw_inconsistent_ontology_exception = false;
    let direct_types = get_types_with_configuration(&onto, &x, true, &cfg)
        .expect("flag-off get_types must return");
    assert!(direct_types.contains(&nothing));
    let found = instances_with_configuration(&onto, &a, false, &cfg)
        .expect("flag-off instances must return");
    assert!(found.contains(&x));
}
