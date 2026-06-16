// Tests for the public query surface under non-default configuration:
//  - FreshEntityPolicy::Disallow is enforced across the `*_with_configuration`
//    query functions.
//  - the inconsistent-ontology throw is applied uniformly to the property-
//    characteristic / subsumption predicates (is_irreflexive / is_reflexive /
//    is_asymmetric / is_transitive / is_object_property_subsumed_by /
//    is_sub_data_property_of / is_symmetric / is_functional).
//  - IncrementalReasoner::is_precomputed reflects precompute state (a flush clears it).
//  - get_disjoint_object_properties(owl:bottomObjectProperty) includes owl:topObjectProperty.

use horned_owl::model::{
    Build, Class, ClassAssertion, ClassExpression as CE, Component, DataProperty,
    DataPropertyAssertion, DisjointClasses, EquivalentClasses, Individual, Literal,
    MutableOntology, NamedIndividual, ObjectProperty, ObjectPropertyAssertion,
    ObjectPropertyExpression as OPE, SameIndividual, SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::configuration::{Configuration, FreshEntityPolicy, IndividualNodeSetPolicy};
use hermit_rs::reasoner::{
    disjoint_classes_with_configuration, equivalent_classes_with_configuration,
    get_disjoint_object_properties, get_types_with_configuration, instance_nodes,
    instance_nodes_with_configuration, instances, instances_with_configuration, is_asymmetric,
    is_concept_satisfiable_with_configuration, is_irreflexive, is_object_property_subsumed_by,
    is_object_property_subsumed_by_with, is_reflexive, is_sub_data_property_of,
    is_sub_data_property_of_with, is_subsumed_by_with_configuration, is_symmetric, is_transitive,
    sub_class_nodes, sub_classes_with_configuration, super_classes_with_configuration, type_nodes,
    InferenceType, IncrementalReasoner, INCONSISTENT_ONTOLOGY_ERROR,
};

type Ae = hermit_rs::structural::A;
type O = SetOntology<Ae>;

fn cls(b: &Build<std::sync::Arc<str>>, n: &str) -> Class<Ae> {
    b.class(format!("http://example.org/{n}"))
}
fn op(b: &Build<std::sync::Arc<str>>, n: &str) -> ObjectProperty<Ae> {
    b.object_property(format!("http://example.org/{n}"))
}
fn dp(b: &Build<std::sync::Arc<str>>, n: &str) -> DataProperty<Ae> {
    b.data_property(format!("http://example.org/{n}"))
}
fn ind(b: &Build<std::sync::Arc<str>>, n: &str) -> NamedIndividual<Ae> {
    b.named_individual(format!("http://example.org/{n}"))
}

/// A small consistent ontology that DECLARES C, a, r, d (each occurs in an axiom, so
/// `isDefined` is true for them) and nothing else.
fn declared_ontology(b: &Build<std::sync::Arc<str>>) -> O {
    let mut o: O = SetOntology::new();
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(cls(b, "C")),
        i: Individual::Named(ind(b, "a")),
    }));
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::ObjectProperty(op(b, "r")),
        from: Individual::Named(ind(b, "a")),
        to: Individual::Named(ind(b, "a")),
    }));
    o.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
        dp: dp(b, "d"),
        from: Individual::Named(ind(b, "a")),
        to: Literal::Datatype {
            datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#string"),
            literal: "x".to_string(),
        },
    }));
    o
}

fn disallow() -> Configuration {
    let mut c = Configuration::default();
    c.fresh_entity_policy = FreshEntityPolicy::Disallow;
    c
}

// ----------------------------------------------------------------------------

#[test]
fn fresh_entity_disallow_enforced_on_free_query_functions() {
    let b = Build::new_arc();
    let o = declared_ontology(&b);
    let cfg = disallow();

    let c = cls(&b, "C");
    let fresh_c = cls(&b, "Fresh");
    let fresh_ind = ind(&b, "fresh-ind");
    let r = OPE::ObjectProperty(op(&b, "r"));
    let fresh_op = OPE::ObjectProperty(op(&b, "freshOp"));
    let d = dp(&b, "d");
    let fresh_dp = dp(&b, "freshDp");

    // Each public *_with_configuration query over a FRESH (undeclared) entity must Err.
    assert!(is_concept_satisfiable_with_configuration(&o, CE::Class(fresh_c.clone()), &cfg).is_err());
    assert!(is_subsumed_by_with_configuration(
        &o,
        CE::Class(fresh_c.clone()),
        CE::Class(c.clone()),
        &cfg
    )
    .is_err());
    assert!(sub_classes_with_configuration(&o, &fresh_c, false, &cfg).is_err());
    assert!(super_classes_with_configuration(&o, &fresh_c, false, &cfg).is_err());
    assert!(equivalent_classes_with_configuration(&o, &fresh_c, &cfg).is_err());
    assert!(disjoint_classes_with_configuration(&o, &fresh_c, &cfg).is_err());
    assert!(get_types_with_configuration(&o, &fresh_ind, false, &cfg).is_err());
    assert!(instances_with_configuration(&o, &fresh_c, false, &cfg).is_err());
    assert!(is_object_property_subsumed_by_with(&o, fresh_op.clone(), r.clone(), &cfg).is_err());
    assert!(is_sub_data_property_of_with(&o, fresh_dp.clone(), d.clone(), &cfg).is_err());

    // The SAME queries over DECLARED entities must succeed under Disallow.
    assert!(is_concept_satisfiable_with_configuration(&o, CE::Class(c.clone()), &cfg).is_ok());
    assert!(sub_classes_with_configuration(&o, &c, false, &cfg).is_ok());
    assert!(get_types_with_configuration(&o, &ind(&b, "a"), false, &cfg).is_ok());
    assert!(instances_with_configuration(&o, &c, false, &cfg).is_ok());
    assert!(is_object_property_subsumed_by_with(&o, r.clone(), r.clone(), &cfg).is_ok());
    assert!(is_sub_data_property_of_with(&o, d.clone(), d.clone(), &cfg).is_ok());
}

#[test]
fn default_allow_policy_accepts_fresh_entities() {
    let b = Build::new_arc();
    let o = declared_ontology(&b);
    let allow = Configuration::default(); // FreshEntityPolicy::Allow
    let fresh_c = cls(&b, "Fresh");
    // Default policy: a fresh class query is accepted (no throw), exactly as before.
    assert!(is_concept_satisfiable_with_configuration(&o, CE::Class(fresh_c.clone()), &allow).is_ok());
    assert!(sub_classes_with_configuration(&o, &fresh_c, false, &allow).is_ok());
}

// ----------------------------------------------------------------------------

fn inconsistent_ontology(b: &Build<std::sync::Arc<str>>) -> O {
    let mut o: O = SetOntology::new();
    o.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(cls(b, "A")),
        CE::Class(cls(b, "B")),
    ])));
    for k in ["A", "B"] {
        o.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(cls(b, k)),
            i: Individual::Named(ind(b, "x")),
        }));
    }
    // also mention r and d so they are declared (irrelevant to inconsistency).
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::ObjectProperty(op(b, "r")),
        from: Individual::Named(ind(b, "x")),
        to: Individual::Named(ind(b, "x")),
    }));
    o
}

#[test]
fn characteristic_and_subsumption_predicates_throw_on_inconsistent() {
    let b = Build::new_arc();
    let o = inconsistent_ontology(&b);
    let r = OPE::ObjectProperty(op(&b, "r"));
    let d = dp(&b, "d");

    macro_rules! assert_inconsistent_err {
        ($e:expr) => {
            match $e {
                Err(msg) => assert_eq!(msg, INCONSISTENT_ONTOLOGY_ERROR, "wrong error"),
                Ok(_) => panic!("expected InconsistentOntology Err, got Ok"),
            }
        };
    }

    // The property-characteristic and subsumption predicates that must throw.
    assert_inconsistent_err!(is_symmetric(&o, r.clone()));
    assert_inconsistent_err!(is_irreflexive(&o, r.clone()));
    assert_inconsistent_err!(is_reflexive(&o, r.clone()));
    assert_inconsistent_err!(is_asymmetric(&o, r.clone()));
    assert_inconsistent_err!(is_transitive(&o, r.clone()));
    assert_inconsistent_err!(is_object_property_subsumed_by(&o, r.clone(), r.clone()));
    assert_inconsistent_err!(is_sub_data_property_of(&o, d.clone(), d.clone()));
}

// ----------------------------------------------------------------------------

#[test]
fn incremental_reasoner_tracks_precomputed_inferences() {
    let b = Build::new_arc();
    let o = declared_ontology(&b);
    let mut r = IncrementalReasoner::new(o);

    assert!(!r.is_precomputed(InferenceType::ClassHierarchy));
    r.precompute(&[InferenceType::ClassHierarchy]).unwrap();
    assert!(r.is_precomputed(InferenceType::ClassHierarchy));
    // A type that was not precomputed stays false.
    assert!(!r.is_precomputed(InferenceType::SameIndividual));

    // A flush that applies a change clears the precompute flags (Java nulls caches).
    r.add_axiom(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(cls(&b, "D")),
        i: Individual::Named(ind(&b, "a")),
    }));
    r.flush();
    assert!(!r.is_precomputed(InferenceType::ClassHierarchy));
}

// ----------------------------------------------------------------------------

#[test]
fn disjoint_object_properties_of_bottom_includes_top() {
    let b = Build::new_arc();
    let mut o: O = SetOntology::new();
    // Declare a property r.
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::ObjectProperty(op(&b, "r")),
        from: Individual::Named(ind(&b, "a")),
        to: Individual::Named(ind(&b, "a")),
    }));
    let bottom = OPE::ObjectProperty(
        b.object_property("http://www.w3.org/2002/07/owl#bottomObjectProperty"),
    );
    let result = get_disjoint_object_properties(&o, &bottom).unwrap();
    // owl:bottomObjectProperty is disjoint from EVERYTHING, so the result must include
    // owl:topObjectProperty (Reasoner.java:1191-1196) — the bug was that it was dropped.
    let top = OPE::ObjectProperty(
        b.object_property("http://www.w3.org/2002/07/owl#topObjectProperty"),
    );
    assert!(
        result.contains(&top),
        "get_disjoint_object_properties(bottom) must include owl:topObjectProperty; got {result:?}"
    );
}

// ----------------------------------------------------------------------------

#[test]
fn equivalent_subclasses_grouped_into_one_node() {
    let b = Build::new_arc();
    let c = cls(&b, "C");
    let d = cls(&b, "D");
    let e = cls(&b, "E");
    let mut o: O = SetOntology::new();
    // D ≡ E, and D ⊑ C, so {D,E} is one equivalence node directly under C.
    o.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(d.clone()),
        CE::Class(e.clone()),
    ])));
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(d.clone()),
        sup: CE::Class(c.clone()),
    }));

    let nodes = sub_class_nodes(&o, &c, true).unwrap();
    // Exactly ONE direct subclass node, containing BOTH D and E (the grouping the flat
    // getter dropped).
    assert_eq!(nodes.len(), 1, "expected one direct subclass node, got {nodes:?}");
    let node = &nodes.nodes()[0];
    assert!(node.contains(&d) && node.contains(&e), "D and E must share one node");
    // flattened() recovers the flat membership.
    let flat = nodes.flattened();
    assert!(flat.contains(&d) && flat.contains(&e));
}

#[test]
fn type_nodes_group_equivalent_types() {
    let b = Build::new_arc();
    let c = cls(&b, "C");
    let d = cls(&b, "D");
    let a = ind(&b, "a");
    let mut o: O = SetOntology::new();
    // C ≡ D, a : C  ->  a's types include the equivalence node {C,D}.
    o.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(c.clone()),
        CE::Class(d.clone()),
    ])));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(c.clone()),
        i: Individual::Named(a.clone()),
    }));

    let nodes = type_nodes(&o, &a, true).unwrap();
    // The direct type node groups C and D together.
    assert!(
        nodes.nodes().iter().any(|n| n.contains(&c) && n.contains(&d)),
        "C and D must be grouped in one type node; got {nodes:?}"
    );
}

#[test]
fn instance_nodes_group_same_individuals_only_under_by_same_as() {
    let b = Build::new_arc();
    let c = cls(&b, "C");
    let a = ind(&b, "a");
    let bb = ind(&b, "b");
    let mut o: O = SetOntology::new();
    // SameIndividual(a, b), a : C  ->  instances(C) = {a, b}.
    o.insert(Component::SameIndividual(SameIndividual(vec![
        Individual::Named(a.clone()),
        Individual::Named(bb.clone()),
    ])));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(c.clone()),
        i: Individual::Named(a.clone()),
    }));

    // Sanity: the flat getter has both.
    let flat = instances(&o, &c, false).unwrap();
    assert!(flat.contains(&a) && flat.contains(&bb));

    // ByName (default): two singleton nodes.
    let by_name = instance_nodes(&o, &c, false).unwrap();
    assert_eq!(by_name.len(), 2, "ByName must keep a and b as separate nodes");
    assert!(by_name.nodes().iter().all(|n| n.len() == 1));

    // BySameAs: a and b collapse into ONE node.
    let mut cfg = Configuration::default();
    cfg.individual_node_set_policy = IndividualNodeSetPolicy::BySameAs;
    let by_same = instance_nodes_with_configuration(&o, &c, false, &cfg).unwrap();
    assert!(
        by_same.nodes().iter().any(|n| n.contains(&a) && n.contains(&bb)),
        "BySameAs must group a and b into one node; got {by_same:?}"
    );
    // Membership is preserved across both policies.
    assert_eq!(by_same.flattened(), flat);
}

#[test]
fn object_property_values_follow_transitive_role_closure() {
    use hermit_rs::reasoner::{get_object_property_values, object_property_instances};
    use horned_owl::model::TransitiveObjectProperty;

    let b = Build::new_arc();
    let r = op(&b, "r");
    let a = ind(&b, "a");
    let bb = ind(&b, "b");
    let cc = ind(&b, "c");
    let mut o: O = SetOntology::new();
    // r(a,b), r(b,c), Transitive(r)  =>  r(a,c) is entailed.
    o.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(
        OPE::ObjectProperty(r.clone()),
    )));
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::ObjectProperty(r.clone()),
        from: Individual::Named(a.clone()),
        to: Individual::Named(bb.clone()),
    }));
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::ObjectProperty(r.clone()),
        from: Individual::Named(bb.clone()),
        to: Individual::Named(cc.clone()),
    }));

    // Forward: a's r-values are {b, c} (c via transitivity).
    let values = get_object_property_values(&o, &a, OPE::ObjectProperty(r.clone())).unwrap();
    assert!(values.contains(&bb), "a r b is asserted");
    assert!(values.contains(&cc), "a r c must follow from transitivity; got {values:?}");

    // The full instance relation contains the transitive pair (a, c).
    let pairs = object_property_instances(&o, OPE::ObjectProperty(r.clone())).unwrap();
    assert!(pairs.contains(&(a.clone(), cc.clone())), "(a,c) transitive pair missing: {pairs:?}");

    // The inverse query: c's Inv(r)-values include a (c is r-reachable from a).
    let inverse =
        get_object_property_values(&o, &cc, OPE::InverseObjectProperty(r.clone())).unwrap();
    assert!(inverse.contains(&a), "Inv(r) of c must include a; got {inverse:?}");
}

#[test]
fn same_individuals_find_cardinality_forced_merge() {
    use hermit_rs::reasoner::get_same_individuals;

    let b = Build::new_arc();
    let r = op(&b, "r");
    let a = ind(&b, "a");
    let bb = ind(&b, "b");
    let cc = ind(&b, "c");
    let thing = b.class("http://www.w3.org/2002/07/owl#Thing");
    let mut o: O = SetOntology::new();
    // a : (<= 1 r),  r(a,b), r(a,c)  =>  b and c must be the same individual.
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectMaxCardinality {
            n: 1,
            ope: OPE::ObjectProperty(r.clone()),
            bce: Box::new(CE::Class(thing)),
        },
        i: Individual::Named(a.clone()),
    }));
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::ObjectProperty(r.clone()),
        from: Individual::Named(a.clone()),
        to: Individual::Named(bb.clone()),
    }));
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::ObjectProperty(r.clone()),
        from: Individual::Named(a.clone()),
        to: Individual::Named(cc.clone()),
    }));

    let same = get_same_individuals(&o, &bb).unwrap();
    assert!(same.contains(&bb), "b is same as itself");
    assert!(same.contains(&cc), "b and c must be inferred same-as; got {same:?}");
}
