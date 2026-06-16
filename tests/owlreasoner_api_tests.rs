// Tests for the OWLReasoner API surface:
// the entailment visitors (EquivalentObjectProperties, EquivalentDataProperties,
// DisjointObjectProperties, DisjointDataProperties, DisjointUnion,
// DatatypeDefinition) and the public Reasoner getters/wrappers ported from
// org.semanticweb.HermiT.Reasoner.

use horned_owl::model::{
    Build, Class, ClassAssertion, ClassExpression as CE, Component, DataProperty,
    DataPropertyAssertion, DataPropertyRange, DataRange, Datatype, DatatypeDefinition,
    DisjointDataProperties, DisjointObjectProperties, DisjointUnion, EquivalentDataProperties,
    EquivalentObjectProperties, Individual, Literal, MutableOntology, NamedIndividual,
    ObjectProperty, ObjectPropertyAssertion, ObjectPropertyDomain, ObjectPropertyExpression as OPE,
    ObjectPropertyRange, SubClassOf, SubObjectPropertyOf, SubObjectPropertyExpression,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner;

type A = hermit_rs::structural::A;

fn class(b: &Build<A>, iri: &str) -> Class<A> {
    b.class(iri)
}
fn op(b: &Build<A>, iri: &str) -> ObjectProperty<A> {
    b.object_property(iri)
}
fn dp(b: &Build<A>, iri: &str) -> DataProperty<A> {
    b.data_property(iri)
}
fn ind(b: &Build<A>, iri: &str) -> NamedIndividual<A> {
    b.named_individual(iri)
}
fn ope(p: ObjectProperty<A>) -> OPE<A> {
    OPE::ObjectProperty(p)
}

// ===========================================================================
// entailment visitors
// ===========================================================================

#[test]
fn entailment_equivalent_object_properties() {
    let b = Build::new_arc();
    let r = op(&b, "http://example.org/r");
    let s = op(&b, "http://example.org/s");
    let mut o: SetOntology<A> = SetOntology::new();
    // r ⊑ s and s ⊑ r  =>  EquivalentObjectProperties(r s) entailed.
    o.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(r.clone())),
        sup: ope(s.clone()),
    }));
    o.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(s.clone())),
        sup: ope(r.clone()),
    }));
    let eq = Component::EquivalentObjectProperties(EquivalentObjectProperties(vec![
        ope(r.clone()),
        ope(s.clone()),
    ]));
    assert!(reasoner::is_entailed(&o, &eq).unwrap());

    // Without the reverse inclusion it is NOT entailed.
    let mut o2: SetOntology<A> = SetOntology::new();
    o2.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(r.clone())),
        sup: ope(s.clone()),
    }));
    assert!(!reasoner::is_entailed(&o2, &eq).unwrap());
}

#[test]
fn entailment_equivalent_data_properties() {
    let b = Build::new_arc();
    let r = dp(&b, "http://example.org/dr");
    let s = dp(&b, "http://example.org/ds");
    use horned_owl::model::SubDataPropertyOf;
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
        sub: r.clone(),
        sup: s.clone(),
    }));
    o.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
        sub: s.clone(),
        sup: r.clone(),
    }));
    let eq = Component::EquivalentDataProperties(EquivalentDataProperties(vec![
        r.clone(),
        s.clone(),
    ]));
    assert!(reasoner::is_entailed(&o, &eq).unwrap());

    let mut o2: SetOntology<A> = SetOntology::new();
    o2.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
        sub: r.clone(),
        sup: s.clone(),
    }));
    assert!(!reasoner::is_entailed(&o2, &eq).unwrap());
}

#[test]
fn entailment_disjoint_object_properties() {
    let b = Build::new_arc();
    let r = op(&b, "http://example.org/r");
    let s = op(&b, "http://example.org/s");
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DisjointObjectProperties(DisjointObjectProperties(
        vec![ope(r.clone()), ope(s.clone())],
    )));
    let concl = Component::DisjointObjectProperties(DisjointObjectProperties(vec![
        ope(r.clone()),
        ope(s.clone()),
    ]));
    assert!(reasoner::is_entailed(&o, &concl).unwrap());

    // No disjointness asserted => not entailed.
    let empty: SetOntology<A> = SetOntology::new();
    assert!(!reasoner::is_entailed(&empty, &concl).unwrap());
}

// FAITHFUL-TO-JAVA: the reference HermiT (1.4.0.0-SNAPSHOT) unconditionally rejects
// owl:topDataProperty in a DataMaxCardinality filler (throwInvalidTopDPUseError), so
// its OWN DisjointDataProperties reduction `∃p.L ⊓ ∃q.L ⊓ ≤1 owl:topDataProperty`
// throws -- the entailment is not answerable in that HermiT. The port reproduces
// this: is_entailed(DisjointDataProperties) returns Err (the same rejection).
#[test]
fn entailment_disjoint_data_properties_errors_like_hermit() {
    let b = Build::new_arc();
    let r = dp(&b, "http://example.org/dr");
    let s = dp(&b, "http://example.org/ds");
    let anchor = ind(&b, "http://example.org/anchor");
    let lit = Literal::Datatype {
        datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#integer"),
        literal: "0".to_string(),
    };
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: r.clone(),
        from: Individual::Named(anchor.clone()),
        to: lit.clone(),
    }));
    o.insert(Component::DisjointDataProperties(DisjointDataProperties(vec![
        r.clone(),
        s.clone(),
    ])));
    let concl = Component::DisjointDataProperties(DisjointDataProperties(vec![
        r.clone(),
        s.clone(),
    ]));
    // Reference HermiT throws on its own reduction; the port returns Err — faithful.
    assert!(reasoner::is_entailed(&o, &concl).is_err());
}

#[test]
fn entailment_disjoint_union() {
    let b = Build::new_arc();
    let c = class(&b, "http://example.org/C");
    let c1 = class(&b, "http://example.org/C1");
    let c2 = class(&b, "http://example.org/C2");
    // Assert exactly the DisjointUnion(C, {C1,C2}) and check it is entailed.
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DisjointUnion(DisjointUnion(
        c.clone(),
        vec![CE::Class(c1.clone()), CE::Class(c2.clone())],
    )));
    let concl = Component::DisjointUnion(DisjointUnion(
        c.clone(),
        vec![CE::Class(c1.clone()), CE::Class(c2.clone())],
    ));
    assert!(reasoner::is_entailed(&o, &concl).unwrap());

    // An empty ontology does not entail the disjoint union.
    let empty: SetOntology<A> = SetOntology::new();
    assert!(!reasoner::is_entailed(&empty, &concl).unwrap());
}

#[test]
fn entailment_datatype_definition() {
    let b = Build::new_arc();
    let dt = Datatype(b.iri("http://example.org/MyInt"));
    let int = Datatype(b.iri("http://www.w3.org/2001/XMLSchema#integer"));
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DatatypeDefinition(DatatypeDefinition {
        kind: dt.clone(),
        range: DataRange::Datatype(int.clone()),
    }));
    let concl = Component::DatatypeDefinition(DatatypeDefinition {
        kind: dt.clone(),
        range: DataRange::Datatype(int.clone()),
    });
    assert!(reasoner::is_entailed(&o, &concl).unwrap());

    // Keeping the same definition (MyInt ≡ integer) in the ontology, a conclusion
    // defining MyInt ≡ string is NOT entailed (integer ≠ string).
    let other = Datatype(b.iri("http://www.w3.org/2001/XMLSchema#string"));
    let concl2 = Component::DatatypeDefinition(DatatypeDefinition {
        kind: dt.clone(),
        range: DataRange::Datatype(other),
    });
    assert!(!reasoner::is_entailed(&o, &concl2).unwrap());
}

// ===========================================================================
// property values / domains / ranges
// ===========================================================================

#[test]
fn object_property_values_basic() {
    let b = Build::new_arc();
    let r = op(&b, "http://example.org/r");
    let a = ind(&b, "http://example.org/a");
    let c = ind(&b, "http://example.org/c");
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope(r.clone()),
        from: Individual::Named(a.clone()),
        to: Individual::Named(c.clone()),
    }));
    let values = reasoner::get_object_property_values(&o, &a, ope(r.clone())).unwrap();
    assert!(values.contains(&c));
    // c has no r-successor.
    let none = reasoner::get_object_property_values(&o, &c, ope(r)).unwrap();
    assert!(none.is_empty());
}

#[test]
fn data_property_values_basic() {
    let b = Build::new_arc();
    let age = dp(&b, "http://example.org/age");
    let a = ind(&b, "http://example.org/a");
    let lit = Literal::Datatype {
        datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#integer"),
        literal: "42".to_string(),
    };
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: age.clone(),
        from: Individual::Named(a.clone()),
        to: lit.clone(),
    }));
    let values = reasoner::get_data_property_values(&o, &a, age.clone()).unwrap();
    assert!(values.contains(&lit));

    // An unrelated property yields nothing.
    let other = dp(&b, "http://example.org/name");
    let none = reasoner::get_data_property_values(&o, &a, other).unwrap();
    assert!(none.is_empty());
}

#[test]
fn object_property_domains_and_ranges() {
    let b = Build::new_arc();
    let r = op(&b, "http://example.org/r");
    let dom = class(&b, "http://example.org/Dom");
    let ran = class(&b, "http://example.org/Ran");
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::ObjectPropertyDomain(ObjectPropertyDomain {
        ope: ope(r.clone()),
        ce: CE::Class(dom.clone()),
    }));
    o.insert(Component::ObjectPropertyRange(ObjectPropertyRange {
        ope: ope(r.clone()),
        ce: CE::Class(ran.clone()),
    }));
    let domains = reasoner::get_object_property_domains(&o, &ope(r.clone()), false).unwrap();
    assert!(domains.contains(&dom));
    let ranges = reasoner::get_object_property_ranges(&o, &ope(r), false).unwrap();
    assert!(ranges.contains(&ran));
}

#[test]
fn data_property_domains_and_ranges() {
    let b = Build::new_arc();
    let age = dp(&b, "http://example.org/age");
    let dom = class(&b, "http://example.org/HasAge");
    let int = Datatype(b.iri("http://www.w3.org/2001/XMLSchema#integer"));
    use horned_owl::model::DataPropertyDomain;
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DataPropertyDomain(DataPropertyDomain {
        dp: age.clone(),
        ce: CE::Class(dom.clone()),
    }));
    o.insert(Component::DataPropertyRange(DataPropertyRange {
        dp: age.clone(),
        dr: DataRange::Datatype(int.clone()),
    }));
    let domains = reasoner::get_data_property_domains(&o, &age, false).unwrap();
    assert!(domains.contains(&dom));
    let ranges = reasoner::get_data_property_ranges(&o, &age).unwrap();
    assert!(ranges.contains(&DataRange::Datatype(int)));
}

// ===========================================================================
// individuals
// ===========================================================================

#[test]
fn same_and_different_individuals() {
    let b = Build::new_arc();
    let a = ind(&b, "http://example.org/a");
    let bb = ind(&b, "http://example.org/b");
    let c = ind(&b, "http://example.org/c");
    use horned_owl::model::{DifferentIndividuals, SameIndividual};
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::SameIndividual(SameIndividual(vec![
        Individual::Named(a.clone()),
        Individual::Named(bb.clone()),
    ])));
    o.insert(Component::DifferentIndividuals(DifferentIndividuals(vec![
        Individual::Named(a.clone()),
        Individual::Named(c.clone()),
    ])));
    let same = reasoner::get_same_individuals(&o, &a).unwrap();
    assert!(same.contains(&a) && same.contains(&bb));
    assert!(!same.contains(&c));

    let diff = reasoner::get_different_individuals(&o, &a).unwrap();
    assert!(diff.contains(&c));
    assert!(!diff.contains(&a));
}

// ===========================================================================
// disjoint / equivalent / inverse properties
// ===========================================================================

#[test]
fn disjoint_object_properties_getter() {
    let b = Build::new_arc();
    let r = op(&b, "http://example.org/r");
    let s = op(&b, "http://example.org/s");
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DisjointObjectProperties(DisjointObjectProperties(
        vec![ope(r.clone()), ope(s.clone())],
    )));
    let disjoint = reasoner::get_disjoint_object_properties(&o, &ope(r.clone())).unwrap();
    assert!(disjoint.contains(&ope(s.clone())));
    assert!(!disjoint.contains(&ope(r.clone())));
}

// HermiT's getDisjointDataProperties GETTER uses a role-assertion
// reduction (NOT the EntailmentChecker's DataMaxCardinality(owl:topDataProperty)
// reduction), so it returns a real answer — unlike `is_entailed(DisjointDataProperties)`
// which faithfully errors (see `entailment_disjoint_data_properties_errors_like_hermit`).
#[test]
fn disjoint_data_properties_getter_returns_answer() {
    let b = Build::new_arc();
    let dr = dp(&b, "http://example.org/dr");
    let ds = dp(&b, "http://example.org/ds");
    let anchor = ind(&b, "http://example.org/anchor");
    let mut od: SetOntology<A> = SetOntology::new();
    od.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: dr.clone(),
        from: Individual::Named(anchor.clone()),
        to: Literal::Datatype {
            datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#integer"),
            literal: "0".to_string(),
        },
    }));
    od.insert(Component::DisjointDataProperties(DisjointDataProperties(vec![
        dr.clone(),
        ds.clone(),
    ])));
    let disjoint = reasoner::get_disjoint_data_properties(&od, &dr).expect("getter must not error");
    assert!(disjoint.contains(&ds), "ds must be disjoint from dr");
    assert!(!disjoint.contains(&dr), "dr is not disjoint from itself");
}

#[test]
fn equivalent_and_inverse_object_properties_getters() {
    let b = Build::new_arc();
    let r = op(&b, "http://example.org/r");
    let s = op(&b, "http://example.org/s");
    let inv = op(&b, "http://example.org/rInv");
    use horned_owl::model::InverseObjectProperties;
    let mut o: SetOntology<A> = SetOntology::new();
    // r ≡ s
    o.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(r.clone())),
        sup: ope(s.clone()),
    }));
    o.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(s.clone())),
        sup: ope(r.clone()),
    }));
    // inv = r⁻
    o.insert(Component::InverseObjectProperties(InverseObjectProperties(
        r.clone(),
        inv.clone(),
    )));
    // getters now return ObjectPropertyExpression nodes (so inverse
    // members survive). The named members r, s are present as OPE::ObjectProperty.
    let eq = reasoner::get_equivalent_object_properties(&o, &ope(r.clone())).unwrap();
    assert!(eq.contains(&ope(r.clone())) && eq.contains(&ope(s.clone())));

    let inverses = reasoner::get_inverse_object_properties(&o, &ope(r.clone())).unwrap();
    assert!(inverses.contains(&ope(inv.clone())));
}

#[test]
fn equivalent_data_properties_getter() {
    let b = Build::new_arc();
    let r = dp(&b, "http://example.org/dr");
    let s = dp(&b, "http://example.org/ds");
    use horned_owl::model::SubDataPropertyOf;
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
        sub: r.clone(),
        sup: s.clone(),
    }));
    o.insert(Component::SubDataPropertyOf(SubDataPropertyOf {
        sub: s.clone(),
        sup: r.clone(),
    }));
    let eq = reasoner::get_equivalent_data_properties(&o, &r).unwrap();
    assert!(eq.contains(&r) && eq.contains(&s));
}

// ===========================================================================
// top/bottom nodes and unsatisfiable classes
// ===========================================================================

#[test]
fn top_bottom_nodes_and_unsatisfiable() {
    let b = Build::new_arc();
    let thing = class(&b, "http://www.w3.org/2002/07/owl#Thing");
    let nothing = class(&b, "http://www.w3.org/2002/07/owl#Nothing");
    let a = class(&b, "http://example.org/A");
    let bcl = class(&b, "http://example.org/B");
    use horned_owl::model::{DisjointClasses, EquivalentClasses};
    let mut o: SetOntology<A> = SetOntology::new();
    // A ⊑ B and A ≡ Thing-ish unsat: make A unsatisfiable: A ⊑ B and A ⊑ ¬B.
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(bcl.clone()),
    }));
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectComplementOf(Box::new(CE::Class(bcl.clone()))),
    }));
    // U ≡ Thing makes U equivalent to owl:Thing (top node member).
    let u = class(&b, "http://example.org/U");
    o.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(u.clone()),
        CE::Class(thing.clone()),
    ])));
    let _ = DisjointClasses::<A>; // keep import path stable

    let top = reasoner::get_top_class_node(&o).unwrap();
    assert!(top.contains(&thing));
    assert!(top.contains(&u));

    let bottom = reasoner::get_bottom_class_node(&o).unwrap();
    assert!(bottom.contains(&nothing));
    assert!(bottom.contains(&a));

    let unsat = reasoner::get_unsatisfiable_classes(&o).unwrap();
    assert!(unsat.contains(&a));
    assert!(!unsat.contains(&bcl));
}

#[test]
fn property_top_bottom_nodes() {
    let b = Build::new_arc();
    let o: SetOntology<A> = SetOntology::new();
    let top_op = op(&b, "http://www.w3.org/2002/07/owl#topObjectProperty");
    let bottom_op = op(&b, "http://www.w3.org/2002/07/owl#bottomObjectProperty");
    // Node getters return ObjectPropertyExpression.
    assert!(reasoner::get_top_object_property_node(&o)
        .unwrap()
        .contains(&ope(top_op.clone())));
    assert!(reasoner::get_bottom_object_property_node(&o)
        .unwrap()
        .contains(&ope(bottom_op.clone())));

    let top_dp = dp(&b, "http://www.w3.org/2002/07/owl#topDataProperty");
    let bottom_dp = dp(&b, "http://www.w3.org/2002/07/owl#bottomDataProperty");
    assert!(reasoner::get_top_data_property_node(&o)
        .unwrap()
        .contains(&top_dp));
    assert!(reasoner::get_bottom_data_property_node(&o)
        .unwrap()
        .contains(&bottom_dp));
}

// ===========================================================================
// has_* wrappers
// ===========================================================================

#[test]
fn has_type_and_relationships() {
    let b = Build::new_arc();
    let r = op(&b, "http://example.org/r");
    let age = dp(&b, "http://example.org/age");
    let c = class(&b, "http://example.org/C");
    let a = ind(&b, "http://example.org/a");
    let d = ind(&b, "http://example.org/d");
    let lit = Literal::Datatype {
        datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#integer"),
        literal: "7".to_string(),
    };
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(c.clone()),
        i: Individual::Named(a.clone()),
    }));
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope(r.clone()),
        from: Individual::Named(a.clone()),
        to: Individual::Named(d.clone()),
    }));
    o.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: age.clone(),
        from: Individual::Named(a.clone()),
        to: lit.clone(),
    }));

    assert!(reasoner::has_type(&o, &a, &c, false).unwrap());
    let other = class(&b, "http://example.org/Other");
    assert!(!reasoner::has_type(&o, &a, &other, false).unwrap());

    assert!(reasoner::has_object_property_relationship(&o, &a, ope(r.clone()), &d).unwrap());
    assert!(!reasoner::has_object_property_relationship(&o, &d, ope(r), &a).unwrap());

    assert!(reasoner::has_data_property_relationship(&o, &a, age.clone(), lit).unwrap());
    let wrong = Literal::Datatype {
        datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#integer"),
        literal: "8".to_string(),
    };
    assert!(!reasoner::has_data_property_relationship(&o, &a, age, wrong).unwrap());
}

// ===========================================================================
// isDefined
// ===========================================================================

#[test]
fn is_defined_entities() {
    let b = Build::new_arc();
    let c = class(&b, "http://example.org/C");
    let r = op(&b, "http://example.org/r");
    let age = dp(&b, "http://example.org/age");
    let a = ind(&b, "http://example.org/a");
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(c.clone()),
        i: Individual::Named(a.clone()),
    }));
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope(r.clone()),
        from: Individual::Named(a.clone()),
        to: Individual::Named(a.clone()),
    }));
    o.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: age.clone(),
        from: Individual::Named(a.clone()),
        to: Literal::Datatype {
            datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#integer"),
            literal: "1".to_string(),
        },
    }));

    assert!(reasoner::is_defined_class(&o, &c).unwrap());
    assert!(reasoner::is_defined_object_property(&o, &r).unwrap());
    assert!(reasoner::is_defined_data_property(&o, &age).unwrap());
    assert!(reasoner::is_defined_individual(&o, &a).unwrap());

    // Undefined entities.
    let undef_c = class(&b, "http://example.org/Undefined");
    assert!(!reasoner::is_defined_class(&o, &undef_c).unwrap());
    let undef_i = ind(&b, "http://example.org/nobody");
    assert!(!reasoner::is_defined_individual(&o, &undef_i).unwrap());

    // owl:Thing is always defined.
    let thing = class(&b, "http://www.w3.org/2002/07/owl#Thing");
    assert!(reasoner::is_defined_class(&o, &thing).unwrap());
}

// ===========================================================================
// metadata, precompute, hierarchy dumps
// ===========================================================================

#[test]
fn reasoner_metadata() {
    assert_eq!(reasoner::reasoner_name(), "HermiT");
    assert_eq!(reasoner::reasoner_version(), "1.4.0.0");
}

#[test]
fn precomputable_inference_types_and_precompute() {
    let types = reasoner::get_precomputable_inference_types();
    assert!(types.contains(&reasoner::InferenceType::ClassHierarchy));
    assert!(types.contains(&reasoner::InferenceType::SameIndividual));
    // DATA_PROPERTY_ASSERTIONS is intentionally NOT precomputable.
    assert_eq!(types.len(), 6);

    let b = Build::new_arc();
    let a = class(&b, "http://example.org/A");
    let bcl = class(&b, "http://example.org/B");
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(bcl.clone()),
    }));
    // Should run without error.
    reasoner::precompute(
        &o,
        &[
            reasoner::InferenceType::ClassHierarchy,
            reasoner::InferenceType::ObjectPropertyHierarchy,
            reasoner::InferenceType::DataPropertyHierarchy,
            reasoner::InferenceType::ClassAssertions,
        ],
    )
    .unwrap();
}

#[test]
fn dump_and_print_hierarchies() {
    let b = Build::new_arc();
    let a = class(&b, "http://example.org/A");
    let bcl = class(&b, "http://example.org/B");
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(bcl.clone()),
    }));
    let dump = reasoner::dump_hierarchies(&o, true, true, true).unwrap();
    // A ⊑ B should appear as a SubClassOf edge.
    assert!(dump.contains("http://example.org/A"));
    assert!(dump.contains("http://example.org/B"));

    let print = reasoner::print_hierarchies(&o, true, false, false).unwrap();
    assert!(print.contains("SubClassOf"));
}

#[test]
fn inconsistent_ontology_getters_throw() {
    let b = Build::new_arc();
    let a = class(&b, "http://example.org/A");
    let ind_a = ind(&b, "http://example.org/x");
    use horned_owl::model::DisjointClasses;
    let mut o: SetOntology<A> = SetOntology::new();
    // A ⊓ ¬A on an individual => inconsistent.
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind_a.clone()),
    }));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(CE::Class(a.clone()))),
        i: Individual::Named(ind_a.clone()),
    }));
    let _ = DisjointClasses::<A>;

    // Default policy: getters that call checkPreConditions throw the distinctive
    // InconsistentOntologyException error.
    let err = reasoner::get_same_individuals(&o, &ind_a).unwrap_err();
    assert_eq!(err, reasoner::INCONSISTENT_ONTOLOGY_ERROR);
    let err2 = reasoner::get_object_property_domains(
        &o,
        &ope(op(&b, "http://example.org/r")),
        false,
    )
    .unwrap_err();
    assert_eq!(err2, reasoner::INCONSISTENT_ONTOLOGY_ERROR);
}

// ===========================================================================
// Regression tests for the parity divergences fixed in this pass.
// ===========================================================================

/// owl:Nothing is disjoint from everything, so it is in every
/// getDisjointClasses result, and a fresh class returns {owl:Nothing}.
#[test]
fn disjoint_classes_includes_owl_nothing() {
    let b = Build::new_arc();
    let cat = class(&b, "http://example.org/Cat");
    let dog = class(&b, "http://example.org/Dog");
    let nothing = class(&b, "http://www.w3.org/2002/07/owl#Nothing");
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DisjointClasses(horned_owl::model::DisjointClasses(vec![
        CE::Class(cat.clone()),
        CE::Class(dog.clone()),
    ])));
    let dis = reasoner::disjoint_classes(&o, &cat).unwrap();
    assert!(dis.contains(&dog));
    assert!(dis.contains(&nothing), "owl:Nothing must be a member");

    // Fresh class absent from the hierarchy -> {owl:Nothing}.
    let fresh = class(&b, "http://example.org/Fresh");
    let dis_fresh = reasoner::disjoint_classes(&o, &fresh).unwrap();
    assert_eq!(dis_fresh, std::iter::once(nothing).collect());
}

/// owl:top/bottomObjectProperty are NOT "defined" (Java's equals arms
/// are dead code).
#[test]
fn op_top_bottom_not_defined() {
    let b = Build::new_arc();
    let o: SetOntology<A> = SetOntology::new();
    let top = op(&b, "http://www.w3.org/2002/07/owl#topObjectProperty");
    let bottom = op(&b, "http://www.w3.org/2002/07/owl#bottomObjectProperty");
    assert_eq!(reasoner::is_defined_object_property(&o, &top), Ok(false));
    assert_eq!(reasoner::is_defined_object_property(&o, &bottom), Ok(false));
}

/// getTypes for an undefined individual returns the full top node
/// (owl:Thing plus every class equivalent to it), not just {owl:Thing}.
#[test]
fn undefined_individual_returns_full_top_node() {
    use horned_owl::model::EquivalentClasses;
    let b = Build::new_arc();
    let thing = class(&b, "http://www.w3.org/2002/07/owl#Thing");
    let d = class(&b, "http://example.org/D");
    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(d.clone()),
        CE::Class(thing.clone()),
    ])));
    let fresh_ind = ind(&b, "http://example.org/fresh");
    let types = reasoner::get_types(&o, &fresh_ind, false).unwrap();
    assert!(types.contains(&thing));
    assert!(types.contains(&d), "Thing-equivalent class D must be included");
}

/// get_super/sub_object_properties exist and respect direct vs
/// transitive over the OPE hierarchy.
#[test]
fn super_sub_object_properties() {
    let b = Build::new_arc();
    let r = op(&b, "http://example.org/r");
    let s = op(&b, "http://example.org/s");
    let t = op(&b, "http://example.org/t");
    let mut o: SetOntology<A> = SetOntology::new();
    for (sub, sup) in [(&r, &s), (&s, &t)] {
        o.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
            sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(sub.clone())),
            sup: ope(sup.clone()),
        }));
    }
    let direct = reasoner::get_super_object_properties(&o, &ope(r.clone()), true).unwrap();
    assert!(direct.contains(&ope(s.clone())));
    assert!(!direct.contains(&ope(t.clone())));
    let all = reasoner::get_super_object_properties(&o, &ope(r.clone()), false).unwrap();
    assert!(all.contains(&ope(s.clone())) && all.contains(&ope(t.clone())));
    let sub = reasoner::get_sub_object_properties(&o, &ope(t.clone()), false).unwrap();
    assert!(sub.contains(&ope(r)) && sub.contains(&ope(s)));
}

/// getInstances over a complex class expression.
#[test]
fn instances_of_expression() {
    let b = Build::new_arc();
    let r = op(&b, "http://example.org/r");
    let c = class(&b, "http://example.org/C");
    let a = ind(&b, "http://example.org/a");
    let x = ind(&b, "http://example.org/x");
    let mut o: SetOntology<A> = SetOntology::new();
    // a r x , x : C  => a : ∃r.C
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope(r.clone()),
        from: Individual::Named(a.clone()),
        to: Individual::Named(x.clone()),
    }));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(c.clone()),
        i: Individual::Named(x.clone()),
    }));
    let ce = CE::ObjectSomeValuesFrom {
        ope: ope(r.clone()),
        bce: Box::new(CE::Class(c.clone())),
    };
    let found = reasoner::instances_of_expression(&o, &ce, false).unwrap();
    assert!(found.contains(&a), "a is an instance of ∃r.C");
    assert!(!found.contains(&x), "x is not an instance of ∃r.C");
}

/// complex-class-expression super/sub/equivalent overloads.
#[test]
fn class_expression_overloads() {
    use horned_owl::model::EquivalentClasses;
    let b = Build::new_arc();
    let c = class(&b, "http://example.org/C");
    let d = class(&b, "http://example.org/D");
    let mut o: SetOntology<A> = SetOntology::new();
    // C ≡ D  =>  C and D are equivalent to the CE (C ⊓ D), so they belong to
    // getEquivalentClasses, NOT getSuperClasses/getSubClasses (which return the
    // STRICT ancestors/descendants, excluding the query node — Reasoner.java:812/823).
    o.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    let thing = class(&b, "http://www.w3.org/2002/07/owl#Thing");
    let ce = CE::ObjectIntersectionOf(vec![CE::Class(c.clone()), CE::Class(d.clone())]);
    let eq = reasoner::equivalent_classes_of_expression(&o, &ce).unwrap();
    assert!(eq.contains(&c) && eq.contains(&d), "C≡D≡(C⊓D)");
    // Strict super-classes exclude the equivalent classes C and D; only owl:Thing remains.
    let supers = reasoner::super_classes_of_expression(&o, &ce, false).unwrap();
    assert!(!supers.contains(&c) && !supers.contains(&d), "equivalents are not super-classes");
    assert!(supers.contains(&thing));
    // Strict sub-classes likewise exclude C and D (they are equivalent, not strict subs).
    let subs = reasoner::sub_classes_of_expression(&o, &ce, false).unwrap();
    assert!(!subs.contains(&c) && !subs.contains(&d), "equivalents are not sub-classes");
}
