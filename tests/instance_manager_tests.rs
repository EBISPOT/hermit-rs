// tests for the read-off `InstanceManager` path.
//
// `realize` / `instances` / `get_types` / `object_property_instances` now build a
// seeded `InstanceManager` by reading the saturated initial-consistency-check
// model (known/possible class instances + same-as), confirming only the POSSIBLE
// instances with the entailment oracle -- mirroring HermiT's
// `InstanceManager.initializeKnowAndPossibleClassInstances` + `realize`.
//
// These tests assert the InstanceManager path produces the SAME answers as the
// old per-pair entailment oracle, on:
//   * known instances (deterministic ABox),
//   * possible instances confirmed (disjunction that always yields the type),
//   * possible instances refuted (disjunction where the type is only one branch),
//   * same-as grouping,
//   * an inconsistent ontology.

use horned_owl::model::{
    Build, Class, ClassAssertion, ClassExpression as CE, Component, DisjointClasses,
    EquivalentClasses, Individual, MutableOntology, NamedIndividual, ObjectPropertyAssertion,
    ObjectPropertyDomain, ObjectPropertyExpression, SameIndividual, SubClassOf,
};
use horned_owl::ontology::set::SetOntology;
use std::collections::HashSet;

use hermit_rs::reasoner::{
    get_types, get_types_with_configuration, instances, instances_with_configuration,
    is_instance_of, object_property_instances, realize, realize_with_configuration,
    INCONSISTENT_ONTOLOGY_ERROR,
};

type A = hermit_rs::structural::A;

fn iris(set: &HashSet<NamedIndividual<A>>) -> Vec<String> {
    let mut v: Vec<String> = set.iter().map(|i| i.0.to_string()).collect();
    v.sort();
    v
}

fn type_iris(set: &HashSet<Class<A>>) -> Vec<String> {
    let mut v: Vec<String> = set.iter().map(|c| c.0.to_string()).collect();
    v.sort();
    v
}

/// Reference oracle for `instances(class, direct=false)`: test each named
/// individual with the standalone `is_instance_of` entailment service. This is the
/// OLD mechanism the InstanceManager path replaces; the two must agree.
fn oracle_instances(
    ontology: &SetOntology<A>,
    class: &Class<A>,
    individuals: &[NamedIndividual<A>],
) -> Vec<String> {
    let mut v: Vec<String> = individuals
        .iter()
        .filter(|i| {
            is_instance_of(ontology, (*i).clone(), CE::Class(class.clone())).unwrap()
        })
        .map(|i| i.0.to_string())
        .collect();
    v.sort();
    v
}

#[test]
fn known_instances_match_oracle() {
    // Deterministic ABox: Dog ⊑ Animal, Dog(rex), Animal(spot). The read-off finds
    // rex's known types {Dog, Animal} and spot's {Animal} directly off the model.
    let build = Build::new_arc();
    let animal = build.class("http://ex/Animal");
    let dog = build.class("http://ex/Dog");
    let rex = build.named_individual("http://ex/rex");
    let spot = build.named_individual("http://ex/spot");

    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(dog.clone()),
        sup: CE::Class(animal.clone()),
    }));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(dog.clone()),
        i: Individual::Named(rex.clone()),
    }));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(animal.clone()),
        i: Individual::Named(spot.clone()),
    }));

    let everyone = vec![rex.clone(), spot.clone()];

    // instances(Animal) = {rex, spot}; instances(Dog) = {rex}.
    assert_eq!(
        iris(&instances(&o, &animal, false).unwrap()),
        oracle_instances(&o, &animal, &everyone)
    );
    assert_eq!(
        iris(&instances(&o, &dog, false).unwrap()),
        oracle_instances(&o, &dog, &everyone)
    );
    assert_eq!(iris(&instances(&o, &dog, false).unwrap()), vec!["http://ex/rex"]);

    // get_types(rex, direct) = {Dog}; get_types(rex, non-direct) ⊇ {Dog, Animal}.
    assert_eq!(
        type_iris(&get_types(&o, &rex, true).unwrap()),
        vec!["http://ex/Dog"]
    );
    let all = type_iris(&get_types(&o, &rex, false).unwrap());
    assert!(all.contains(&"http://ex/Dog".to_string()));
    assert!(all.contains(&"http://ex/Animal".to_string()));
    assert!(all.contains(&"http://www.w3.org/2002/07/owl#Thing".to_string()));

    // realize: rex's direct type is Dog, spot's is Animal.
    let r = realize(&o).unwrap();
    assert_eq!(type_iris(&r[&rex]), vec!["http://ex/Dog"]);
    assert_eq!(type_iris(&r[&spot]), vec!["http://ex/Animal"]);
}

#[test]
fn possible_instance_confirmed_matches_oracle() {
    // A disjunction every branch of which entails the type: A ⊑ C, B ⊑ C,
    // (A ⊔ B)(x). x is a non-deterministic (possible) member of A and of B but a
    // *confirmed* instance of C. The read-off marks C possible on x's node; the
    // realize oracle confirms it.
    let build = Build::new_arc();
    let a = build.class("http://ex/A");
    let b = build.class("http://ex/B");
    let c = build.class("http://ex/C");
    let x = build.named_individual("http://ex/x");

    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(a.clone()),
        sup: CE::Class(c.clone()),
    }));
    o.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(b.clone()),
        sup: CE::Class(c.clone()),
    }));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectUnionOf(vec![CE::Class(a.clone()), CE::Class(b.clone())]),
        i: Individual::Named(x.clone()),
    }));

    let everyone = vec![x.clone()];

    // x is a confirmed instance of C (every disjunct yields C).
    assert_eq!(
        iris(&instances(&o, &c, false).unwrap()),
        oracle_instances(&o, &c, &everyone)
    );
    assert_eq!(iris(&instances(&o, &c, false).unwrap()), vec!["http://ex/x"]);
    // x is NOT a (certain) instance of A alone.
    assert_eq!(
        iris(&instances(&o, &a, false).unwrap()),
        oracle_instances(&o, &a, &everyone)
    );
    assert!(iris(&instances(&o, &a, false).unwrap()).is_empty());

    // get_types(x) includes C but not A or B.
    let all = type_iris(&get_types(&o, &x, false).unwrap());
    assert!(all.contains(&"http://ex/C".to_string()));
    assert!(!all.contains(&"http://ex/A".to_string()));
    assert!(!all.contains(&"http://ex/B".to_string()));
}

#[test]
fn possible_instance_refuted_matches_oracle() {
    // A disjunction where the candidate type is only ONE branch:
    // (A ⊔ B)(x), A and B disjoint. The model may put A (or its consequences) on
    // x's node non-deterministically, seeding A as a *possible* instance; the
    // realize oracle then REFUTES it (x is not a certain instance of A).
    let build = Build::new_arc();
    let a = build.class("http://ex/A");
    let b = build.class("http://ex/B");
    let x = build.named_individual("http://ex/x");

    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::DisjointClasses(DisjointClasses(vec![
        CE::Class(a.clone()),
        CE::Class(b.clone()),
    ])));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectUnionOf(vec![CE::Class(a.clone()), CE::Class(b.clone())]),
        i: Individual::Named(x.clone()),
    }));

    let everyone = vec![x.clone()];

    // x is a certain instance of NEITHER A nor B (each is only one branch).
    assert_eq!(
        iris(&instances(&o, &a, false).unwrap()),
        oracle_instances(&o, &a, &everyone)
    );
    assert!(iris(&instances(&o, &a, false).unwrap()).is_empty());
    assert_eq!(
        iris(&instances(&o, &b, false).unwrap()),
        oracle_instances(&o, &b, &everyone)
    );
    assert!(iris(&instances(&o, &b, false).unwrap()).is_empty());
    // The only certain type of x is owl:Thing.
    assert_eq!(
        type_iris(&get_types(&o, &x, false).unwrap()),
        vec!["http://www.w3.org/2002/07/owl#Thing"]
    );
}

#[test]
fn same_as_grouping_is_correct() {
    // SameIndividual(a, b), A(a). The same-as read-off groups {a, b}; both must be
    // instances of A (a directly, b via the merge). This checks the same-as path
    // (`initializeSameAs` / `computeSameAsEquivalenceClasses`) gives the same
    // answers as the entailment oracle.
    let build = Build::new_arc();
    let cls_a = build.class("http://ex/A");
    let a = build.named_individual("http://ex/a");
    let b = build.named_individual("http://ex/b");

    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::SameIndividual(SameIndividual(vec![
        Individual::Named(a.clone()),
        Individual::Named(b.clone()),
    ])));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(cls_a.clone()),
        i: Individual::Named(a.clone()),
    }));

    let everyone = vec![a.clone(), b.clone()];

    // Both a and b are instances of A (same-as), matching the oracle.
    assert_eq!(
        iris(&instances(&o, &cls_a, false).unwrap()),
        oracle_instances(&o, &cls_a, &everyone)
    );
    let answer = iris(&instances(&o, &cls_a, false).unwrap());
    assert!(answer.contains(&"http://ex/a".to_string()));
    assert!(answer.contains(&"http://ex/b".to_string()));
}

#[test]
fn object_property_instances_match_oracle() {
    // owns(alice, fido), domain(owns)=Person. The role read-off finds the known
    // pair (alice, fido); object_property_instances returns it.
    let build = Build::new_arc();
    let owns = build.object_property("http://ex/owns");
    let person = build.class("http://ex/Person");
    let alice = build.named_individual("http://ex/alice");
    let fido = build.named_individual("http://ex/fido");
    let ope = ObjectPropertyExpression::ObjectProperty(owns.clone());

    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::ObjectPropertyDomain(ObjectPropertyDomain {
        ope: ope.clone(),
        ce: CE::Class(person.clone()),
    }));
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ope.clone(),
        from: Individual::Named(alice.clone()),
        to: Individual::Named(fido.clone()),
    }));

    let pairs = object_property_instances(&o, ope.clone()).unwrap();
    let pair_iris: HashSet<(String, String)> = pairs
        .iter()
        .map(|(f, t)| (f.0.to_string(), t.0.to_string()))
        .collect();
    assert!(pair_iris.contains(&("http://ex/alice".to_string(), "http://ex/fido".to_string())));
    // And alice is a Person via the domain (a known/possible class instance).
    let people = iris(&instances(&o, &person, false).unwrap());
    assert!(people.contains(&"http://ex/alice".to_string()));
}

#[test]
fn inconsistent_ontology_every_individual_is_instance_of_everything() {
    // A ⊑ ⊥ (A equivalent to Nothing) with A(a) makes the ontology inconsistent.
    // HermiT's `getInstances` then returns ALL named individuals for any class, and
    // `getTypes` returns the classified bottom node, which on an inconsistent
    // ontology holds every (non-internal) class in the signature
    // (`InstanceManager.getTypes` returns `singleton(bottomNode)`). The
    // InstanceManager path mirrors `setInconsistent` and must reproduce this.
    let build = Build::new_arc();
    let a = build.class("http://ex/A");
    let nothing = build.class("http://www.w3.org/2002/07/owl#Nothing");
    let unrelated = build.class("http://ex/Unrelated");
    let ind = build.named_individual("http://ex/ind");

    let mut o: SetOntology<A> = SetOntology::new();
    o.insert(Component::EquivalentClasses(EquivalentClasses(vec![
        CE::Class(a.clone()),
        CE::Class(nothing.clone()),
    ])));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a.clone()),
        i: Individual::Named(ind.clone()),
    }));

    // under the default flag the queries throw InconsistentOntologyException.
    assert_eq!(
        instances(&o, &unrelated, false).unwrap_err(),
        INCONSISTENT_ONTOLOGY_ERROR
    );
    assert_eq!(get_types(&o, &ind, true).unwrap_err(), INCONSISTENT_ONTOLOGY_ERROR);
    assert_eq!(realize(&o).unwrap_err(), INCONSISTENT_ONTOLOGY_ERROR);

    // Flag OFF: the degenerate return behaviour (the InstanceManager's `setInconsistent`).
    let mut cfg = hermit_rs::configuration::Configuration::default();
    cfg.throw_inconsistent_ontology_exception = false;
    // Every individual is an instance of every class (here `Unrelated`).
    assert_eq!(
        iris(&instances_with_configuration(&o, &unrelated, false, &cfg).unwrap()),
        vec!["http://ex/ind"]
    );
    // Direct types are the bottom node = every class in the signature.
    assert_eq!(
        type_iris(&get_types_with_configuration(&o, &ind, true, &cfg).unwrap()),
        vec![
            "http://ex/A",
            "http://www.w3.org/2002/07/owl#Nothing",
            "http://www.w3.org/2002/07/owl#Thing"
        ]
    );
    // realize maps the individual to every class in the signature.
    let r = realize_with_configuration(&o, &cfg).unwrap();
    assert_eq!(
        type_iris(&r[&ind]),
        vec![
            "http://ex/A",
            "http://www.w3.org/2002/07/owl#Nothing",
            "http://www.w3.org/2002/07/owl#Thing"
        ]
    );
}
