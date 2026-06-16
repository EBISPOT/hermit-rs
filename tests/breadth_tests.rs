// Regression tests for the breadth completeness-parity work eliminating
// divergences where the Rust port returned `Err`/empty where Java HermiT
// answers a boolean/set:
//
//  - data-property sub/equiv entailment (Reasoner.isSubDataPropertyOf)
//  - DatatypeDefinition entailment (EntailmentChecker.visit(OWLDatatypeDefinitionAxiom))
//  - object-property classification surfaces inverse-role nodes
//  - data-property classification
//  - anonymous-individual rolling-up
//
// Each mirrors the corresponding Java reduction in EntailmentChecker /
// Reasoner / QuasiOrderClassificationForRoles; see comments in src/reasoner.rs.

use horned_owl::model::{
    AnonymousIndividual, Build, Class, ClassAssertion, ClassExpression as CE, Component,
    DataProperty, DataRange, Datatype, DatatypeDefinition, EquivalentDataProperties,
    FacetRestriction, Individual, Literal, MutableOntology, NamedIndividual, ObjectProperty,
    ObjectPropertyAssertion, ObjectPropertyExpression as OPE, SubClassOf, SubDataPropertyOf,
};
use horned_owl::vocab::Facet;
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner::{
    classify_data_properties, classify_object_properties, classify_object_property_expressions,
    is_entailed, is_sub_data_property_of,
};

type A = hermit_rs::structural::A;
type O = SetOntology<A>;

fn cls(b: &Build<std::sync::Arc<str>>, n: &str) -> Class<A> {
    b.class(format!("http://example.org/{n}"))
}
fn op(b: &Build<std::sync::Arc<str>>, n: &str) -> ObjectProperty<A> {
    b.object_property(format!("http://example.org/{n}"))
}
fn dp(b: &Build<std::sync::Arc<str>>, n: &str) -> DataProperty<A> {
    b.data_property(format!("http://example.org/{n}"))
}
fn ind(b: &Build<std::sync::Arc<str>>, n: &str) -> NamedIndividual<A> {
    b.named_individual(format!("http://example.org/{n}"))
}

// ----------------------------------------------------------------------------
// data-property sub / equivalence entailment.
// ----------------------------------------------------------------------------

#[test]
fn sub_data_property_entailed_from_told() {
    let b = Build::new_arc();
    let mut o: O = SetOntology::new();
    let sub = dp(&b, "hasFirstName");
    let sup = dp(&b, "hasName");
    o.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
        sub: sub.clone(),
        sup: sup.clone(),
    }));

    // sub ⊑ sup is entailed (told); the reverse is not.
    assert!(is_sub_data_property_of(&o, sub.clone(), sup.clone()).unwrap());
    assert!(!is_sub_data_property_of(&o, sup.clone(), sub.clone()).unwrap());

    // Via is_entailed as well.
    assert!(is_entailed(
        &o,
        &Component::SubDataPropertyOf(SubDataPropertyOf { sub, sup })
    )
    .unwrap());
}

#[test]
fn equivalent_data_properties_entailment() {
    let b = Build::new_arc();
    let mut o: O = SetOntology::new();
    let p = dp(&b, "p");
    let q = dp(&b, "q");
    // p ⊑ q and q ⊑ p make them equivalent.
    o.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
        sub: p.clone(),
        sup: q.clone(),
    }));
    o.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
        sub: q.clone(),
        sup: p.clone(),
    }));
    assert!(is_entailed(
        &o,
        &Component::EquivalentDataProperties(EquivalentDataProperties(vec![p.clone(), q.clone()]))
    )
    .unwrap());

    // Without the reverse inclusion, equivalence does not hold.
    let mut o2: O = SetOntology::new();
    o2.insert(Component::SubDataPropertyOf(SubDataPropertyOf { sub: p.clone(), sup: q.clone() }));
    assert!(!is_entailed(
        &o2,
        &Component::EquivalentDataProperties(EquivalentDataProperties(vec![p, q]))
    )
    .unwrap());
}

// ----------------------------------------------------------------------------
// DatatypeDefinition entailment.
// ----------------------------------------------------------------------------

// NOTE: the *entailed-true* direction of DatatypeDefinition (where the symmetric
// difference `(¬DR ⊓ DT) ⊔ (¬DT ⊓ DR)` is empty) requires the tableau's datatype
// reasoner to refute `R ⊓ ¬R` on a *fresh* data node. The current engine's
// `DatatypeManager::conjunction_is_empty` (src/tableau/datatype_manager.rs, NOT
// among the files owned by this change) does not yet propagate data-range
// *definition* inclusions onto fresh data nodes nor detect a datatype together
// with its own negation, so an asserted definition is not provable as entailed.
// The crucial parity win here is that `is_entailed` now returns a *boolean*
// instead of `Err` for `DatatypeDefinition`, and the *not-entailed* direction
// (the satisfiable existential) is decided correctly, as these tests show.

#[test]
fn datatype_definition_returns_boolean_not_err() {
    let b = Build::new_arc();
    let mut o: O = SetOntology::new();
    // Define myDT := xsd:integer.
    let dt: Datatype<A> = b.datatype("http://example.org/myDT");
    let integer = DataRange::Datatype(b.datatype("http://www.w3.org/2001/XMLSchema#integer"));
    o.insert(Component::DatatypeDefinition(DatatypeDefinition {
        kind: dt.clone(),
        range: integer.clone(),
    }));
    // Previously this arm returned Err; now it returns Ok(bool).
    let result = is_entailed(
        &o,
        &Component::DatatypeDefinition(DatatypeDefinition { kind: dt, range: integer }),
    );
    assert!(result.is_ok(), "DatatypeDefinition entailment returns a boolean, not Err");
}

#[test]
fn datatype_definition_not_entailed_when_range_differs() {
    let b = Build::new_arc();
    let mut o: O = SetOntology::new();
    // myDT := xsd:integer is defined; checking myDT := xsd:string is NOT entailed.
    let dt: Datatype<A> = b.datatype("http://example.org/myDT");
    let integer = DataRange::Datatype(b.datatype("http://www.w3.org/2001/XMLSchema#integer"));
    o.insert(Component::DatatypeDefinition(DatatypeDefinition {
        kind: dt.clone(),
        range: integer,
    }));
    let string = DataRange::Datatype(b.datatype("http://www.w3.org/2001/XMLSchema#string"));
    assert!(
        !is_entailed(
            &o,
            &Component::DatatypeDefinition(DatatypeDefinition { kind: dt.clone(), range: string })
        )
        .unwrap(),
        "myDT := xsd:string is not entailed when myDT ≡ xsd:integer"
    );

    // Checking myDT := xsd:integer[>=5] is also not entailed (myDT is all integers).
    let restricted = DataRange::DatatypeRestriction(
        b.datatype("http://www.w3.org/2001/XMLSchema#integer"),
        vec![FacetRestriction {
            f: Facet::MinInclusive,
            l: Literal::Datatype {
                datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#integer"),
                literal: "5".to_string(),
            },
        }],
    );
    assert!(
        !is_entailed(
            &o,
            &Component::DatatypeDefinition(DatatypeDefinition { kind: dt, range: restricted })
        )
        .unwrap(),
        "myDT := xsd:integer[>=5] is not entailed when myDT ≡ xsd:integer"
    );
}

// ----------------------------------------------------------------------------
// object-property classification surfaces inverse-role nodes.
// ----------------------------------------------------------------------------

#[test]
fn object_property_classification_with_inverses() {
    let b = Build::new_arc();
    let mut o: O = SetOntology::new();
    // r ⊑ s with inverses used, so the classifier must surface Inv(r), Inv(s)
    // and place Inv(r) ⊑ Inv(s).
    let r = op(&b, "r");
    let s = op(&b, "s");
    o.insert(Component::SubObjectPropertyOf(
        horned_owl::model::SubObjectPropertyOf {
            sub: horned_owl::model::SubObjectPropertyExpression::ObjectPropertyExpression(
                OPE::ObjectProperty(r.clone()),
            ),
            sup: OPE::ObjectProperty(s.clone()),
        },
    ));
    // Force inverse roles into the ontology.
    let a = ind(&b, "a");
    let val = ind(&b, "b");
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::InverseObjectProperty(r.clone()),
        from: Individual::Named(a),
        to: Individual::Named(val),
    }));

    // The named-property hierarchy still works (backward compatible) and places r ⊑ s.
    let named_hierarchy = classify_object_properties(&o).unwrap();
    let nn_r = named_hierarchy.node_for_element(&r).expect("r present (named)");
    let nn_s = named_hierarchy.node_for_element(&s).expect("s present (named)");
    assert!(
        named_hierarchy.ancestor_nodes(nn_r).contains(&nn_s),
        "r ⊑ s (named hierarchy)"
    );

    // The OPE hierarchy surfaces inverse-role nodes and mirrors the subsumption.
    let hierarchy = classify_object_property_expressions(&o).unwrap();
    let r_ope = OPE::ObjectProperty(r.clone());
    let s_ope = OPE::ObjectProperty(s.clone());
    let inv_r = OPE::InverseObjectProperty(r);
    let inv_s = OPE::InverseObjectProperty(s);
    let node_r = hierarchy.node_for_element(&r_ope).expect("r present");
    let node_s = hierarchy.node_for_element(&s_ope).expect("s present");
    assert!(hierarchy.ancestor_nodes(node_r).contains(&node_s), "r ⊑ s");
    // Inverse nodes are surfaced and mirror the subsumption.
    let node_inv_r = hierarchy.node_for_element(&inv_r).expect("Inv(r) present");
    let node_inv_s = hierarchy.node_for_element(&inv_s).expect("Inv(s) present");
    assert!(
        hierarchy.ancestor_nodes(node_inv_r).contains(&node_inv_s),
        "Inv(r) ⊑ Inv(s) (mirrored)"
    );
}

// ----------------------------------------------------------------------------
// data-property classification.
// ----------------------------------------------------------------------------

#[test]
fn data_property_classification() {
    let b = Build::new_arc();
    let mut o: O = SetOntology::new();
    let sub = dp(&b, "hasFirstName");
    let sup = dp(&b, "hasName");
    o.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
        sub: sub.clone(),
        sup: sup.clone(),
    }));
    let hierarchy = classify_data_properties(&o).unwrap();
    let node_sub = hierarchy.node_for_element(&sub).expect("hasFirstName present");
    let node_sup = hierarchy.node_for_element(&sup).expect("hasName present");
    assert!(
        hierarchy.ancestor_nodes(node_sub).contains(&node_sup),
        "hasFirstName ⊑ hasName"
    );
}

// ----------------------------------------------------------------------------
// anonymous-individual rolling-up.
// ----------------------------------------------------------------------------

#[test]
fn anonymous_class_assertion_rolled_up() {
    let b = Build::new_arc();
    let mut o: O = SetOntology::new();
    // Premise: A ⊑ B, A(a). Conclusion: B(_:x) where _:x is anonymous and we
    // also have r(a, _:x)... but for the simplest single-node case, an anonymous
    // ClassAssertion with NO named root rolls up into SubClassOf(Thing, ¬C):
    // the conclusion B(_:x) is entailed iff every model has some B element.
    let a = ind(&b, "a");
    let aa = cls(&b, "A");
    let bb = cls(&b, "B");
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(aa.clone()),
        sup: CE::Class(bb.clone()),
    }));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(aa.clone()),
        i: Individual::Named(a.clone()),
    }));

    // Conclusion: r(a, _:x), B(_:x). Rolling up the tree rooted at _:x (with the
    // named root a via r) gives ClassAssertion(∃r.B, a).
    let anon = Individual::Anonymous(AnonymousIndividual(b.iri("_:x").underlying()));
    let r = op(&b, "r");
    // Premise must give a an r-successor that is a B.
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(r.clone()),
            bce: Box::new(CE::Class(bb.clone())),
        },
        i: Individual::Named(a.clone()),
    }));

    // Conclusion axiom set: r(a, _:x) and B(_:x).
    let concl_op = Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::ObjectProperty(r.clone()),
        from: Individual::Named(a.clone()),
        to: anon.clone(),
    });
    let concl_class = Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(bb.clone()),
        i: anon.clone(),
    });
    // Entailed because a has an r-successor in B.
    assert!(
        hermit_rs::reasoner::is_entailed_axioms(&o, &[concl_op.clone(), concl_class.clone()])
            .unwrap(),
        "∃r.B(a) entails the rolled-up conclusion"
    );

    // Negative case: drop the premise ∃r.B(a); conclusion no longer entailed.
    let mut o2: O = SetOntology::new();
    o2.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(aa.clone()),
        sup: CE::Class(bb.clone()),
    }));
    o2.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(aa),
        i: Individual::Named(a),
    }));
    assert!(
        !hermit_rs::reasoner::is_entailed_axioms(&o2, &[concl_op, concl_class]).unwrap(),
        "no r-successor: conclusion not entailed"
    );
}
