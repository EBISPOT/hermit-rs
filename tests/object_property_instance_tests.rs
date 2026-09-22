//! Property-instance read-off must agree with exhaustive entailment, including
//! pairs absent from one chosen model and names joined by uncertain equality.
use hermit_rs::reasoner::{
    get_object_property_values, is_entailed, object_property_instances, INCONSISTENT_ONTOLOGY_ERROR,
};
use horned_owl::model::{
    AnnotatedComponent, Build, Component, Individual, ObjectPropertyAssertion,
    ObjectPropertyExpression as OPE,
};
use horned_owl::ontology::{component_mapped::ComponentMappedOntology, set::SetOntology};
use std::collections::HashSet;

type A = hermit_rs::structural::A;

fn load(body: &str) -> SetOntology<A> {
    let text = format!(
        "Prefix(:=<http://ex/>) Prefix(owl:=<http://www.w3.org/2002/07/owl#>) Ontology({body})"
    );
    let (onto, _): (ComponentMappedOntology<A, AnnotatedComponent<A>>, _) =
        horned_owl::io::ofn::reader::read_with_build(
            &mut std::io::Cursor::new(text),
            &Build::new_arc(),
        )
        .unwrap();
    onto.into()
}

/// Check the full extension, its inverse, and every subject's values against
/// independent negative-assertion consistency tests, including all non-instances.
fn check_against_oracle(body: &str, individuals: &[&str], property: &str) {
    let ontology = load(body);
    let build = Build::new_arc();
    let role = build.object_property(property);
    let individuals: Vec<_> = individuals
        .iter()
        .map(|name| build.named_individual(format!("http://ex/{name}")))
        .collect();
    for ope in [
        OPE::ObjectProperty(role.clone()),
        OPE::InverseObjectProperty(role),
    ] {
        let mut expected = HashSet::new();
        for from in &individuals {
            for to in &individuals {
                if is_entailed(
                    &ontology,
                    &Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
                        ope: ope.clone(),
                        from: Individual::Named(from.clone()),
                        to: Individual::Named(to.clone()),
                    }),
                )
                .unwrap()
                {
                    expected.insert((from.clone(), to.clone()));
                }
            }
        }
        assert_eq!(
            object_property_instances(&ontology, ope.clone()).unwrap(),
            expected,
            "property {ope:?} in {body}"
        );
        // Explicitly declaring the property also exercises the values API for
        // empty/fresh extensions without relying on a declaration's absence.
        for individual in &individuals {
            let expected_values: HashSet<_> = expected
                .iter()
                .filter(|(from, _)| from == individual)
                .map(|(_, to)| to.clone())
                .collect();
            assert_eq!(
                get_object_property_values(&ontology, individual, ope.clone()).unwrap(),
                expected_values,
                "values for {individual:?} via {ope:?} in {body}"
            );
        }
    }
}

#[test]
fn simple_role_hierarchy_and_absent_pairs() {
    check_against_oracle(
        "SubObjectPropertyOf(:p :r) ObjectPropertyAssertion(:p :a :b)
         Declaration(NamedIndividual(:c))",
        &["a", "b", "c"],
        "http://ex/r",
    );
}

#[test]
fn deterministic_merges_preserve_every_name() {
    for complex in ["", "TransitiveObjectProperty(:r)"] {
        check_against_oracle(
            &format!(
                "ObjectPropertyAssertion(:r :a :b) SameIndividual(:a :aa)
                 SameIndividual(:b :bb) {complex}"
            ),
            &["a", "aa", "b", "bb"],
            "http://ex/r",
        );
    }
}

#[test]
fn functional_roles_expand_entailed_equalities() {
    check_against_oracle(
        "FunctionalObjectProperty(:p) ObjectPropertyAssertion(:p :a :b)
         ObjectPropertyAssertion(:p :a :bb) ObjectPropertyAssertion(:r :b :c)",
        &["a", "b", "bb", "c"],
        "http://ex/r",
    );
}

#[test]
fn nondeterministic_merges_do_not_certify_role_instances() {
    // The old one-name-per-node projection randomly selected x/y as the owner
    // of the deterministic r(a,c) tuple, incorrectly returning r(x,c)/r(a,y).
    // Exercise either endpoint and both, on simple and complex roles.
    for complex in ["", "TransitiveObjectProperty(:r)"] {
        for merges in [
            "ClassAssertion(ObjectOneOf(:a :b) :x)",
            "ClassAssertion(ObjectOneOf(:c :b) :y)",
            "ClassAssertion(ObjectOneOf(:a :b) :x) ClassAssertion(ObjectOneOf(:c :b) :y)",
        ] {
            check_against_oracle(
                &format!(
                    "ObjectPropertyAssertion(:r :a :c) Declaration(NamedIndividual(:b))
                     Declaration(NamedIndividual(:x)) Declaration(NamedIndividual(:y))
                     {merges} {complex}"
                ),
                &["a", "b", "c", "x", "y"],
                "http://ex/r",
            );
        }
    }
}

#[test]
fn possible_pairs_are_confirmed_or_refuted() {
    // Both choices imply r(a,b), while neither p(a,b) nor q(a,b) is certain.
    // The possible pair present in the chosen branch must be tested, not
    // returned as known or discarded along with the absent pairs.
    let body = "SubObjectPropertyOf(:p :r) SubObjectPropertyOf(:q :r)
        ClassAssertion(ObjectUnionOf(ObjectHasValue(:p :b) ObjectHasValue(:q :b)) :a)
        Declaration(NamedIndividual(:c))";
    for role in ["http://ex/p", "http://ex/q", "http://ex/r"] {
        check_against_oracle(body, &["a", "b", "c"], role);
    }
}

#[test]
fn complex_roles_follow_chains_and_uncertain_edges() {
    let body = "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)
        ObjectPropertyAssertion(:q :b :c)
        ClassAssertion(ObjectUnionOf(ObjectHasValue(:p :b) ObjectHasValue(:s :b)) :a)";
    check_against_oracle(body, &["a", "b", "c"], "http://ex/r");
    check_against_oracle(
        &format!("{body} SubObjectPropertyOf(:s :p)"),
        &["a", "b", "c"],
        "http://ex/r",
    );
    check_against_oracle(
        "TransitiveObjectProperty(:r) ObjectPropertyAssertion(:r :a :b)
         ObjectPropertyAssertion(:r :b :c) SameIndividual(:c :cc)",
        &["a", "b", "c", "cc"],
        "http://ex/r",
    );
}

#[test]
fn reflexive_and_top_equivalent_roles() {
    check_against_oracle(
        "ReflexiveObjectProperty(:r) Declaration(NamedIndividual(:a))
         Declaration(NamedIndividual(:b))",
        &["a", "b"],
        "http://ex/r",
    );
    check_against_oracle(
        "EquivalentObjectProperties(:r owl:topObjectProperty)
         Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))",
        &["a", "b"],
        "http://ex/r",
    );
}

#[test]
fn top_bottom_and_empty_roles() {
    for property in ["topObjectProperty", "bottomObjectProperty"] {
        let iri = format!("http://www.w3.org/2002/07/owl#{property}");
        check_against_oracle(
            &format!(
                "Declaration(ObjectProperty(owl:{property}))
                 Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))"
            ),
            &["a", "b"],
            &iri,
        );
        // No declaration: the built-in still has its specified extension.
        let onto = load("Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))");
        let pairs = object_property_instances(
            &onto,
            OPE::ObjectProperty(Build::new_arc().object_property(iri.as_str())),
        )
        .unwrap();
        assert_eq!(
            pairs.len(),
            if property == "topObjectProperty" {
                4
            } else {
                0
            }
        );
    }
    check_against_oracle(
        "Declaration(ObjectProperty(:r)) Declaration(NamedIndividual(:a))",
        &["a"],
        "http://ex/r",
    );
    check_against_oracle("", &[], "http://ex/fresh");
}

#[test]
fn anonymous_individuals_are_not_returned() {
    check_against_oracle(
        "TransitiveObjectProperty(:r) ObjectPropertyAssertion(:r :a _:anon)
         ObjectPropertyAssertion(:r _:anon :b)",
        &["a", "b"],
        "http://ex/r",
    );
}

#[test]
fn inconsistent_ontology_throws_even_for_builtins_or_empty_abox() {
    for body in [
        "SubClassOf(owl:Thing owl:Nothing)",
        "SubClassOf(owl:Thing owl:Nothing) TransitiveObjectProperty(:r)",
        "ClassAssertion(owl:Nothing :a)",
    ] {
        let ontology = load(body);
        for iri in [
            "http://ex/r",
            "http://www.w3.org/2002/07/owl#topObjectProperty",
            "http://www.w3.org/2002/07/owl#bottomObjectProperty",
        ] {
            assert_eq!(
                object_property_instances(
                    &ontology,
                    OPE::ObjectProperty(Build::new_arc().object_property(iri)),
                )
                .unwrap_err(),
                INCONSISTENT_ONTOLOGY_ERROR
            );
        }
    }
}
