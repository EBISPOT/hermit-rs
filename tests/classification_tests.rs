// Classification tests: build the subsumption hierarchy of an ontology's named
// classes and check parent/child/equivalence structure.

use horned_owl::model::{
    Build, Class, ClassExpression as CE, Component, EquivalentClasses, MutableOntology, SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::hierarchy::Hierarchy;
use hermit_rs::reasoner::classify;

type A = hermit_rs::structural::A;

fn node_equiv_iris(hierarchy: &Hierarchy<Class<A>>, node: usize) -> Vec<String> {
    let mut v: Vec<String> = hierarchy
        .node(node)
        .equivalent_elements()
        .iter()
        .map(|c| c.0.to_string())
        .collect();
    v.sort();
    v
}

/// Whether `sub_iri`'s node is a descendant of `sup_iri`'s node (proper or
/// equivalent) in the hierarchy.
fn is_ancestor(hierarchy: &Hierarchy<Class<A>>, sup_iri: &str, sub_iri: &str, build: &Build<A>) -> bool {
    let sub_class = build.class(sub_iri);
    let sup_class = build.class(sup_iri);
    let sub_node = hierarchy.node_for_element(&sub_class).unwrap();
    let sup_node = hierarchy.node_for_element(&sup_class).unwrap();
    hierarchy.ancestor_nodes(sub_node).contains(&sup_node)
}

#[test]
fn deterministic_classification_multi_parent_and_equivalence() {
    // Exercises the deterministic (Horn) single-model classification path: subsumers
    // are read off one model per concept. Includes multiple inheritance, transitive
    // subsumption, equivalence (via mutual SubClassOf), and an existential (still
    // Horn). The result must match the pairwise build.
    let build = Build::new_arc();
    let mk = |n: &str| build.class(format!("http://example.org/{n}"));
    let (animal, mammal, dog, cat, pet, canine) =
        (mk("Animal"), mk("Mammal"), mk("Dog"), mk("Cat"), mk("Pet"), mk("Canine"));

    let mut o: SetOntology<_> = SetOntology::new();
    let sub = |o: &mut SetOntology<A>, s: &Class<A>, p: &Class<A>| {
        o.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(s.clone()),
            sup: CE::Class(p.clone()),
        }));
    };
    sub(&mut o, &mammal, &animal);
    sub(&mut o, &dog, &mammal);
    sub(&mut o, &cat, &mammal);
    sub(&mut o, &dog, &pet); // multiple inheritance: Dog ⊑ Mammal and Dog ⊑ Pet
    // Dog ≡ Canine via mutual inclusion.
    sub(&mut o, &dog, &canine);
    sub(&mut o, &canine, &dog);

    let h = classify(&o).unwrap();

    // Transitive and multi-parent ancestry.
    assert!(is_ancestor(&h, "http://example.org/Mammal", "http://example.org/Dog", &build));
    assert!(is_ancestor(&h, "http://example.org/Animal", "http://example.org/Dog", &build));
    assert!(is_ancestor(&h, "http://example.org/Pet", "http://example.org/Dog", &build));
    assert!(is_ancestor(&h, "http://example.org/Animal", "http://example.org/Cat", &build));
    // Cat is not under Pet.
    assert!(!is_ancestor(&h, "http://example.org/Pet", "http://example.org/Cat", &build));
    // Dog and Canine are equivalent (same hierarchy node).
    let dog_node = h.node_for_element(&dog).unwrap();
    assert!(node_equiv_iris(&h, dog_node).contains(&"http://example.org/Canine".to_string()));
}

#[test]
fn classifies_a_linear_chain() {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");

    // A ⊑ B ⊑ C
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::Class(c.clone()),
    }));

    let hierarchy = classify(&ontology).unwrap();

    // Ancestry: A < B < C < Thing; and the transitive A < C.
    assert!(is_ancestor(&hierarchy, "http://example.org/B", "http://example.org/A", &build));
    assert!(is_ancestor(&hierarchy, "http://example.org/C", "http://example.org/B", &build));
    assert!(is_ancestor(&hierarchy, "http://example.org/C", "http://example.org/A", &build));
    assert!(is_ancestor(
        &hierarchy,
        "http://www.w3.org/2002/07/owl#Thing",
        "http://example.org/C",
        &build
    ));

    // B is a *direct* child of C (transitive reduction) but A is not.
    let c_node = hierarchy.node_for_element(&c).unwrap();
    let b_node = hierarchy.node_for_element(&b).unwrap();
    let a_node = hierarchy.node_for_element(&a).unwrap();
    assert!(hierarchy.node(c_node).child_nodes().contains(&b_node));
    assert!(!hierarchy.node(c_node).child_nodes().contains(&a_node));
}

#[test]
fn equivalent_classes_share_a_node() {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");

    // A ≡ B
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));

    let hierarchy = classify(&ontology).unwrap();
    let a_node = hierarchy.node_for_element(&a).unwrap();
    let b_node = hierarchy.node_for_element(&b).unwrap();
    assert_eq!(a_node, b_node);
    assert_eq!(
        node_equiv_iris(&hierarchy, a_node),
        vec!["http://example.org/A".to_string(), "http://example.org/B".to_string()]
    );
}

#[test]
fn unsatisfiable_class_collapses_to_bottom() {
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");

    // A ⊑ B and A ⊑ ¬B  ->  A is unsatisfiable (equivalent to owl:Nothing).
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::ObjectComplementOf(Box::new(CE::Class(b.clone()))),
    }));

    let hierarchy = classify(&ontology).unwrap();
    let a_node = hierarchy.node_for_element(&a).unwrap();
    assert_eq!(a_node, hierarchy.bottom_node());
}

#[test]
fn realises_direct_types() {
    use horned_owl::model::{ClassAssertion, Individual};
    use hermit_rs::reasoner::realize;

    let build = Build::new_arc();
    let animal = build.class("http://example.org/Animal");
    let dog = build.class("http://example.org/Dog");
    let rex = build.named_individual("http://example.org/rex");

    // Dog ⊑ Animal, Dog(rex). Direct type of rex is Dog (not Animal, which is
    // an inferred but non-direct type).
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(dog.clone()),
        sup: CE::Class(animal.clone()),
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(dog.clone()),
        i: Individual::Named(rex.clone()),
    }));

    let types = realize(&ontology).unwrap();
    let rex_types: Vec<String> = {
        let mut v: Vec<String> =
            types[&rex].iter().map(|c| c.0.to_string()).collect();
        v.sort();
        v
    };
    assert_eq!(rex_types, vec!["http://example.org/Dog".to_string()]);
}

#[test]
fn realises_inferred_type_via_domain() {
    use horned_owl::model::{
        Individual, ObjectPropertyAssertion, ObjectPropertyDomain, ObjectPropertyExpression,
    };
    use hermit_rs::reasoner::realize;

    let build = Build::new_arc();
    let person = build.class("http://example.org/Person");
    let owns = build.object_property("http://example.org/owns");
    let alice = build.named_individual("http://example.org/alice");
    let thing = build.named_individual("http://example.org/thing1");
    let ope = ObjectPropertyExpression::ObjectProperty(owns.clone());

    // domain(owns) = Person, owns(alice, thing1). Alice is inferred a Person.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::ObjectPropertyDomain(ObjectPropertyDomain {
        ope: ope.clone(),
        ce: CE::Class(person.clone()),
    }));
    ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(alice.clone()),
        to: Individual::Named(thing.clone()),
    }));

    let types = realize(&ontology).unwrap();
    assert!(types[&alice].contains(&person));
}

#[test]
fn object_property_subsumption_basic() {
    use horned_owl::model::{ObjectPropertyExpression, SubObjectPropertyExpression, SubObjectPropertyOf};
    use hermit_rs::reasoner::is_object_property_subsumed_by;

    let build = Build::new_arc();
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let t = build.object_property("http://example.org/t");
    let r_e = ObjectPropertyExpression::ObjectProperty(r.clone());
    let s_e = ObjectPropertyExpression::ObjectProperty(s.clone());
    let t_e = ObjectPropertyExpression::ObjectProperty(t.clone());

    // r ⊑ s
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(r_e.clone()),
        sup: s_e.clone(),
    }));

    assert!(is_object_property_subsumed_by(&ontology, r_e.clone(), s_e.clone()).unwrap());
    assert!(!is_object_property_subsumed_by(&ontology, s_e.clone(), r_e.clone()).unwrap());
    // r is not subsumed by an unrelated t.
    assert!(!is_object_property_subsumed_by(&ontology, r_e.clone(), t_e.clone()).unwrap());
}

#[test]
fn classifies_object_property_hierarchy() {
    use horned_owl::model::{
        EquivalentObjectProperties, ObjectProperty, ObjectPropertyExpression,
        SubObjectPropertyExpression, SubObjectPropertyOf,
    };
    use hermit_rs::reasoner::classify_object_properties;

    let build = Build::new_arc();
    let r = build.object_property("http://example.org/r");
    let s = build.object_property("http://example.org/s");
    let p = build.object_property("http://example.org/p");
    let q = build.object_property("http://example.org/q");
    let ope = |op: &ObjectProperty<A>| ObjectPropertyExpression::ObjectProperty(op.clone());

    // r ⊑ s, and p ≡ q.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(&r)),
        sup: ope(&s),
    }));
    ontology.insert(Component::EquivalentObjectProperties(EquivalentObjectProperties(vec![
        ope(&p),
        ope(&q),
    ])));

    let hierarchy = classify_object_properties(&ontology).unwrap();

    // r is a descendant of s.
    let r_node = hierarchy.node_for_element(&r).unwrap();
    let s_node = hierarchy.node_for_element(&s).unwrap();
    assert!(hierarchy.ancestor_nodes(r_node).contains(&s_node));
    assert_ne!(r_node, s_node);

    // p and q are equivalent -> same node.
    let p_node = hierarchy.node_for_element(&p).unwrap();
    let q_node = hierarchy.node_for_element(&q).unwrap();
    assert_eq!(p_node, q_node);

    // Everything sits under owl:topObjectProperty.
    let top = build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty");
    let top_node = hierarchy.node_for_element(&top).unwrap();
    assert!(hierarchy.ancestor_nodes(s_node).contains(&top_node));
}

#[test]
fn told_subsumers_classify_consistently() {
    // A told chain plus an *inferred* (non-told) subsumption: A ⊑ B (told),
    // B ⊑ C (told), and C ⊑ D entailed only via C ⊑ ∃r.Self-free reasoning is
    // hard to set up; instead use an equivalence to force an inferred edge:
    // D ≡ A means D and A share a node, and D inherits A's told subsumers.
    use horned_owl::model::EquivalentClasses;
    let build = Build::new_arc();
    let a = build.class("http://example.org/A");
    let b = build.class("http://example.org/B");
    let c = build.class("http://example.org/C");
    let d = build.class("http://example.org/D");

    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(b.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::Class(c.clone()),
    }));
    ontology.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(d.clone()),
        CE::Class(a.clone()),
    ])));

    let hierarchy = classify(&ontology).unwrap();
    // D ≡ A -> same node, and that node is below B and (transitively) C.
    let a_node = hierarchy.node_for_element(&a).unwrap();
    let d_node = hierarchy.node_for_element(&d).unwrap();
    assert_eq!(a_node, d_node);
    let b_node = hierarchy.node_for_element(&b).unwrap();
    let c_node = hierarchy.node_for_element(&c).unwrap();
    assert!(hierarchy.ancestor_nodes(a_node).contains(&b_node));
    assert!(hierarchy.ancestor_nodes(a_node).contains(&c_node));
}

#[test]
fn class_query_api() {
    use horned_owl::model::{DisjointClasses, EquivalentClasses};
    use hermit_rs::reasoner::{
        disjoint_classes, equivalent_classes, sub_classes, super_classes,
    };

    let build = Build::new_arc();
    let animal = build.class("http://example.org/Animal");
    let dog = build.class("http://example.org/Dog");
    let cat = build.class("http://example.org/Cat");
    let hound = build.class("http://example.org/Hound");

    // Dog ⊑ Animal, Cat ⊑ Animal, Hound ≡ Dog, Disjoint(Dog, Cat).
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(dog.clone()),
        sup: CE::Class(animal.clone()),
    }));
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(cat.clone()),
        sup: CE::Class(animal.clone()),
    }));
    ontology.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(hound.clone()),
        CE::Class(dog.clone()),
    ])));
    ontology.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(dog.clone()),
        CE::Class(cat.clone()),
    ])));

    // Equivalents: Dog and Hound.
    let equ = equivalent_classes(&ontology, &dog).unwrap();
    assert!(equ.contains(&dog) && equ.contains(&hound));

    // Direct superclasses of Dog: Animal.
    let sup = super_classes(&ontology, &dog, true).unwrap();
    assert!(sup.contains(&animal));

    // Direct subclasses of Animal: Dog (≡ Hound) and Cat.
    let sub = sub_classes(&ontology, &animal, true).unwrap();
    assert!(sub.contains(&dog) && sub.contains(&hound) && sub.contains(&cat));

    // Disjoint with Dog: Cat.
    let dis = disjoint_classes(&ontology, &dog).unwrap();
    assert!(dis.contains(&cat));
    assert!(!dis.contains(&animal));
}

#[test]
fn instance_query_api() {
    use horned_owl::model::{ClassAssertion, Individual};
    use hermit_rs::reasoner::instances;

    let build = Build::new_arc();
    let animal = build.class("http://example.org/Animal");
    let dog = build.class("http://example.org/Dog");
    let rex = build.named_individual("http://example.org/rex");
    let generic = build.named_individual("http://example.org/generic");

    // Dog ⊑ Animal, Dog(rex), Animal(generic).
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(dog.clone()),
        sup: CE::Class(animal.clone()),
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(dog.clone()),
        i: Individual::Named(rex.clone()),
    }));
    ontology.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(animal.clone()),
        i: Individual::Named(generic.clone()),
    }));

    // All instances of Animal: both rex (inferred) and generic.
    let all_animals = instances(&ontology, &animal, false).unwrap();
    assert!(all_animals.contains(&rex) && all_animals.contains(&generic));

    // Direct instances of Animal: only generic (rex's direct type is Dog).
    let direct_animals = instances(&ontology, &animal, true).unwrap();
    assert!(direct_animals.contains(&generic));
    assert!(!direct_animals.contains(&rex));

    // All instances of Dog: just rex.
    let dogs = instances(&ontology, &dog, false).unwrap();
    assert!(dogs.contains(&rex) && !dogs.contains(&generic));
}

#[test]
fn object_property_instances_retrieval() {
    use horned_owl::model::{
        Individual, ObjectPropertyAssertion, ObjectPropertyExpression, SubObjectPropertyExpression,
        SubObjectPropertyOf,
    };
    use hermit_rs::reasoner::object_property_instances;

    let build = Build::new_arc();
    let knows = build.object_property("http://example.org/knows");
    let likes = build.object_property("http://example.org/likes");
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");
    let knows_e = ObjectPropertyExpression::ObjectProperty(knows.clone());
    let likes_e = ObjectPropertyExpression::ObjectProperty(likes.clone());

    // likes ⊑ knows, likes(a,b): so knows(a,b) is entailed.
    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(likes_e.clone()),
        sup: knows_e.clone(),
    }));
    ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: likes_e.clone(),
        from: Individual::Named(a.clone()),
        to: Individual::Named(b.clone()),
    }));

    let knows_pairs = object_property_instances(&ontology, knows_e).unwrap();
    assert!(knows_pairs.contains(&(a.clone(), b.clone())));
    assert!(!knows_pairs.contains(&(b.clone(), a.clone())));
}

#[test]
fn entailment_of_property_and_class_axioms() {
    use horned_owl::model::{
        DisjointUnion, FunctionalObjectProperty, InverseObjectProperties, ObjectPropertyDomain,
        ObjectPropertyExpression, ObjectPropertyRange, SubClassOf, SymmetricObjectProperty,
    };
    use hermit_rs::reasoner::is_entailed;

    let build = Build::new_arc();
    let person = build.class("http://example.org/Person");
    let agent = build.class("http://example.org/Agent");
    let parent = build.object_property("http://example.org/parent");
    let child = build.object_property("http://example.org/child");
    let married = build.object_property("http://example.org/married");
    let parent_e = ObjectPropertyExpression::ObjectProperty(parent.clone());
    let child_e = ObjectPropertyExpression::ObjectProperty(child.clone());
    let married_e = ObjectPropertyExpression::ObjectProperty(married.clone());

    let mut ontology: SetOntology<_> = SetOntology::new();
    // Person ⊑ Agent.
    ontology.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(person.clone()),
        sup: CE::Class(agent.clone()),
    }));
    // domain(parent) = Person, range(parent) = Person.
    ontology.insert(Component::ObjectPropertyDomain(ObjectPropertyDomain {
        ope: parent_e.clone(),
        ce: CE::Class(person.clone()),
    }));
    ontology.insert(Component::ObjectPropertyRange(ObjectPropertyRange {
        ope: parent_e.clone(),
        ce: CE::Class(person.clone()),
    }));
    // parent ≡ Inv(child).
    ontology.insert(Component::InverseObjectProperties(InverseObjectProperties(
        horned_owl::model::ObjectPropertyExpression::ObjectProperty(parent.clone()),
        horned_owl::model::ObjectPropertyExpression::ObjectProperty(child.clone()),
    )));
    // married symmetric and functional.
    ontology.insert(Component::SymmetricObjectProperty(SymmetricObjectProperty(married_e.clone())));
    ontology.insert(Component::FunctionalObjectProperty(FunctionalObjectProperty(married_e.clone())));

    // domain(parent) ⊒ Agent is *not* asserted, but domain(parent) ⊒ Person is.
    assert!(is_entailed(
        &ontology,
        &Component::ObjectPropertyDomain(ObjectPropertyDomain {
            ope: parent_e.clone(),
            ce: CE::Class(person.clone()),
        })
    )
    .unwrap());
    // range(parent) = Person is entailed.
    assert!(is_entailed(
        &ontology,
        &Component::ObjectPropertyRange(ObjectPropertyRange {
            ope: parent_e.clone(),
            ce: CE::Class(person.clone()),
        })
    )
    .unwrap());
    // parent ≡ Inv(child) is entailed.
    assert!(is_entailed(
        &ontology,
        &Component::InverseObjectProperties(InverseObjectProperties(
            horned_owl::model::ObjectPropertyExpression::ObjectProperty(parent.clone()),
            horned_owl::model::ObjectPropertyExpression::ObjectProperty(child.clone()),
        ))
    )
    .unwrap());
    // married symmetric/functional are entailed.
    assert!(is_entailed(
        &ontology,
        &Component::SymmetricObjectProperty(SymmetricObjectProperty(married_e.clone()))
    )
    .unwrap());
    assert!(is_entailed(
        &ontology,
        &Component::FunctionalObjectProperty(FunctionalObjectProperty(married_e.clone()))
    )
    .unwrap());
    // child is *not* symmetric.
    assert!(!is_entailed(
        &ontology,
        &Component::SymmetricObjectProperty(SymmetricObjectProperty(child_e.clone()))
    )
    .unwrap());

    // A DisjointUnion axiom: Agent = Person ⊔ Robot with the two disjoint.
    let robot = build.class("http://example.org/Robot");
    let mut ont2: SetOntology<_> = SetOntology::new();
    ont2.insert(Component::DisjointUnion(DisjointUnion(
        agent.clone(),
        vec![CE::Class(person.clone()), CE::Class(robot.clone())],
    )));
    assert!(is_entailed(
        &ont2,
        &Component::DisjointUnion(DisjointUnion(
            agent.clone(),
            vec![CE::Class(person.clone()), CE::Class(robot.clone())],
        ))
    )
    .unwrap());

    // DisjointObjectProperties: parent and child are made disjoint; entailment
    // holds once the axiom is asserted, and fails for unrelated props.
    use horned_owl::model::DisjointObjectProperties;
    let mut ont3: SetOntology<_> = SetOntology::new();
    ont3.insert(Component::DisjointObjectProperties(DisjointObjectProperties(vec![
        parent_e.clone(),
        married_e.clone(),
    ])));
    assert!(is_entailed(
        &ont3,
        &Component::DisjointObjectProperties(DisjointObjectProperties(vec![
            parent_e.clone(),
            married_e.clone(),
        ]))
    )
    .unwrap());
    // child and parent are not asserted disjoint -> not entailed.
    assert!(!is_entailed(
        &ont3,
        &Component::DisjointObjectProperties(DisjointObjectProperties(vec![
            parent_e.clone(),
            child_e.clone(),
        ]))
    )
    .unwrap());
}

#[test]
fn property_characteristic_and_individual_queries() {
    use horned_owl::model::{
        FunctionalObjectProperty, Individual, ObjectPropertyExpression, SameIndividual,
        SymmetricObjectProperty,
    };
    use hermit_rs::reasoner::{is_functional, is_same_individual, is_symmetric};

    let build = Build::new_arc();
    let married = build.object_property("http://example.org/married");
    let knows = build.object_property("http://example.org/knows");
    let married_e = ObjectPropertyExpression::ObjectProperty(married.clone());
    let knows_e = ObjectPropertyExpression::ObjectProperty(knows.clone());
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");

    let mut ontology: SetOntology<_> = SetOntology::new();
    ontology.insert(Component::SymmetricObjectProperty(SymmetricObjectProperty(married_e.clone())));
    ontology.insert(Component::FunctionalObjectProperty(FunctionalObjectProperty(married_e.clone())));
    ontology.insert(Component::SameIndividual(SameIndividual(vec![
        Individual::Named(a.clone()),
        Individual::Named(b.clone()),
    ])));

    assert!(is_symmetric(&ontology, married_e.clone()).unwrap());
    assert!(!is_symmetric(&ontology, knows_e.clone()).unwrap());
    assert!(is_functional(&ontology, married_e.clone()).unwrap());
    assert!(!is_functional(&ontology, knows_e.clone()).unwrap());
    assert!(is_same_individual(&ontology, a.clone(), b.clone()).unwrap());
}

// ----------------------------------------------------------------------------
// RESIDUAL 1: Configuration threaded through classification.
//
// HermiT's `m_configuration` governs ALL reasoning, classification included. The
// `*_with_configuration` classify variants must run classification under a chosen
// `Configuration` (blocking strategy, expansion strategy, ...) while producing the
// SAME (sound + complete) classification answers as the default. We classify the
// same ontology under several non-default configurations and assert the resulting
// hierarchies are identical to the default one.
// ----------------------------------------------------------------------------

/// Builds a small mixed ontology: a Horn part (a chain Dog ⊑ Mammal ⊑ Animal,
/// Hound ≡ Dog) plus a non-deterministic part (Disjoint(Dog, Cat) and a
/// disjunction Pet ⊑ Dog ⊔ Cat) so both the deterministic and the quasi-order
/// classification paths can be exercised.
fn mixed_ontology() -> SetOntology<A> {
    use horned_owl::model::{DisjointClasses, EquivalentClasses};
    let build = Build::new_arc();
    let mk = |n: &str| build.class(format!("http://example.org/{n}"));
    let (animal, mammal, dog, cat, hound, pet) =
        (mk("Animal"), mk("Mammal"), mk("Dog"), mk("Cat"), mk("Hound"), mk("Pet"));

    let mut o: SetOntology<A> = SetOntology::new();
    let mut sub = |s: &Class<A>, p: &Class<A>| {
        o.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(s.clone()),
            sup: CE::Class(p.clone()),
        }));
    };
    sub(&mammal, &animal);
    sub(&dog, &mammal);
    sub(&cat, &mammal);
    // Pet ⊑ Dog ⊔ Cat -- a disjunction, makes the ontology non-deterministic.
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(pet.clone()),
        sup: CE::ObjectUnionOf(vec![CE::Class(dog.clone()), CE::Class(cat.clone())]),
    }));
    o.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(hound.clone()),
        CE::Class(dog.clone()),
    ])));
    o.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(dog.clone()),
        CE::Class(cat.clone()),
    ])));
    o
}

/// A canonical, comparable rendering of a class hierarchy: for each element, the
/// sorted set of its (all) super-elements. Two hierarchies are logically equal
/// iff this map is equal, regardless of node identity / iteration order.
fn hierarchy_signature(h: &Hierarchy<Class<A>>) -> std::collections::BTreeMap<String, Vec<String>> {
    let mut sig = std::collections::BTreeMap::new();
    for element in h.all_elements() {
        let mut supers: Vec<String> = h
            .super_elements(element, false)
            .iter()
            .map(|c| c.0.to_string())
            .collect();
        supers.sort();
        sig.insert(element.0.to_string(), supers);
    }
    sig
}

#[test]
fn classification_answers_are_configuration_invariant() {
    use hermit_rs::configuration::{
        BlockingStrategyType, Configuration, ExistentialStrategyType,
    };
    use hermit_rs::reasoner::{classify, classify_with_configuration};

    let ontology = mixed_ontology();

    // The default classification (== HermiT defaults) is the reference answer.
    let default_h = classify(&ontology).unwrap();
    let reference = hierarchy_signature(&default_h);
    // Sanity: the reference is non-trivial.
    assert!(reference.len() >= 6, "expected the mixed ontology's classes");

    // A set of non-default configurations, each tuning the tableau differently.
    let mut configs: Vec<Configuration> = Vec::new();

    let mut ancestor_blocking = Configuration::default();
    ancestor_blocking.blocking_strategy_type = BlockingStrategyType::Ancestor;
    configs.push(ancestor_blocking);

    let mut individual_reuse = Configuration::default();
    individual_reuse.existential_strategy_type = ExistentialStrategyType::IndividualReuse;
    configs.push(individual_reuse);

    let mut no_disjunction_learning = Configuration::default();
    no_disjunction_learning.use_disjunction_learning = false;
    configs.push(no_disjunction_learning);

    let mut force_quasi = Configuration::default();
    force_quasi.force_quasi_order_classification = true;
    configs.push(force_quasi);

    for config in &configs {
        let h = classify_with_configuration(&ontology, config).unwrap();
        assert_eq!(
            hierarchy_signature(&h),
            reference,
            "classification under {:?}/{:?} must match the default answer",
            config.blocking_strategy_type,
            config.existential_strategy_type,
        );
    }

    // And the default-config variant is byte-for-byte the same as `classify`.
    let via_default_config =
        classify_with_configuration(&ontology, &Configuration::default()).unwrap();
    assert_eq!(hierarchy_signature(&via_default_config), reference);
}

// ----------------------------------------------------------------------------
// RESIDUAL 2: classification progress monitor exposed.
//
// Java's `classifyClasses` fires `ClassificationProgressMonitor.elementClassified`
// once per classified concept. `classify_with_monitor` must surface this: the
// supplied monitor receives exactly one `element_classified` call per element of
// the classified hierarchy.
// ----------------------------------------------------------------------------

#[test]
fn classify_with_monitor_fires_once_per_classified_element() {
    use hermit_rs::hierarchy::ClassificationProgressMonitor;
    use hermit_rs::reasoner::{classify, classify_with_monitor};

    let ontology = mixed_ontology();

    // A monitor that records every classified element (Java's elementClassified).
    struct Recorder {
        seen: Vec<String>,
    }
    impl ClassificationProgressMonitor<Class<A>> for Recorder {
        fn element_classified(&mut self, element: &Class<A>) {
            self.seen.push(element.0.to_string());
        }
    }

    let mut recorder = Recorder { seen: Vec::new() };
    let hierarchy = classify_with_monitor(&ontology, &mut recorder).unwrap();

    // Exactly one callback per element of the classified hierarchy (incl. owl:Thing
    // and owl:Nothing), with no duplicates.
    let mut reported = recorder.seen.clone();
    reported.sort();
    let mut unique = reported.clone();
    unique.dedup();
    assert_eq!(
        reported, unique,
        "the monitor must fire at most once per element"
    );

    let mut elements: Vec<String> =
        hierarchy.all_elements().map(|c| c.0.to_string()).collect();
    elements.sort();
    assert_eq!(
        reported, elements,
        "the monitor must fire exactly once per classified element"
    );

    // The answer is unchanged versus the no-monitor `classify`.
    let plain = classify(&ontology).unwrap();
    assert_eq!(hierarchy_signature(&hierarchy), hierarchy_signature(&plain));
}

// Exercises the batched non-subsumer test: with six object properties (one told
// subsumption r1 ⊑ r2, the rest unrelated), classifying r1 leaves enough unknown
// possible subsumers (3..=6) to trigger the union test, which must conclude r1 is
// not subsumed by the unrelated properties while preserving the told r1 ⊑ r2.
#[test]
fn batched_non_subsumer_test_in_object_property_classification() {
    use horned_owl::model::{
        DeclareObjectProperty, ObjectProperty, ObjectPropertyExpression,
        SubObjectPropertyExpression, SubObjectPropertyOf,
    };
    use hermit_rs::reasoner::classify_object_properties;

    let build = Build::new_arc();
    let ops: Vec<ObjectProperty<A>> = (1..=6)
        .map(|i| build.object_property(format!("http://example.org/r{i}")))
        .collect();
    let ope =
        |op: &ObjectProperty<A>| ObjectPropertyExpression::ObjectProperty(op.clone());

    let mut ontology: SetOntology<A> = SetOntology::new();
    // Declare all six so they are classified (3..=6 unknown possibles trigger the
    // batched test); r1 ⊑ r2, the rest unrelated.
    for op in &ops {
        ontology.insert(Component::DeclareObjectProperty(DeclareObjectProperty(op.clone())));
    }
    ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SubObjectPropertyExpression::ObjectPropertyExpression(ope(&ops[0])),
        sup: ope(&ops[1]),
    }));

    let hierarchy = classify_object_properties(&ontology).unwrap();
    let top = build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty");
    let r1 = hierarchy.node_for_element(&ops[0]).unwrap();
    let r2 = hierarchy.node_for_element(&ops[1]).unwrap();
    let top_node = hierarchy.node_for_element(&top).unwrap();
    let ancestors = hierarchy.ancestor_nodes(r1);
    // r1 ⊑ r2 (told) survives, and everything sits under top.
    assert!(ancestors.contains(&r2));
    assert!(ancestors.contains(&top_node));
    // r1 is NOT subsumed by any of the unrelated r3..r6.
    for op in &ops[2..] {
        let node = hierarchy.node_for_element(op).unwrap();
        assert!(!ancestors.contains(&node), "r1 must not be subsumed by {}", op.0);
    }
}
