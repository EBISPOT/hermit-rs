//! Property-instance read-off must agree with exhaustive entailment, including
//! pairs absent from one chosen model and names joined by uncertain equality.
use hermit_rs::reasoner::{
    get_object_property_values, is_entailed, object_property_instances, IncrementalReasoner,
    ObjectPropertyInstanceIndex, INCONSISTENT_ONTOLOGY_ERROR,
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
        horned_owl::io::ofn::reader::read(
            &mut std::io::Cursor::new(text),
            horned_owl::io::ParserConfiguration::new(Build::new_arc()),
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
    let mut index = ObjectPropertyInstanceIndex::new(&ontology).unwrap();
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
        assert_eq!(
            index.object_property_instances(ope.clone()).unwrap(),
            expected
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
fn nondeterministic_merges_can_entail_simple_role_instances() {
    // The converse of the test above. x is a or b, and both have r to c, so
    // r(x,c) is entailed although x only shares that tuple through the merge
    // the model chose. Likewise y is c or d and a has r to both, so r(a,y) is
    // entailed, while r(x,d), r(x,f) and r(b,y) hold only under one choice.
    // These alias pairs are possible: skipping one as absent loses an answer.
    // one_index_handles_several_complex_roles_and_uncertain_aliases covers
    // aliases of complex roles, which are read off marker concepts instead.
    let body = "ClassAssertion(ObjectOneOf(:a :b) :x) ClassAssertion(ObjectOneOf(:c :d) :y)
        ObjectPropertyAssertion(:r :a :c) ObjectPropertyAssertion(:r :b :c)
        ObjectPropertyAssertion(:r :a :d) ObjectPropertyAssertion(:r :b :f)";
    check_against_oracle(body, &["a", "b", "c", "d", "f", "x", "y"], "http://ex/r");
    let build = Build::new_arc();
    let pairs = object_property_instances(
        &load(body),
        OPE::ObjectProperty(build.object_property("http://ex/r")),
    )
    .unwrap();
    let has = |from: &str, to: &str| {
        pairs.contains(&(
            build.named_individual(format!("http://ex/{from}")),
            build.named_individual(format!("http://ex/{to}")),
        ))
    };
    assert!(has("x", "c") && has("a", "y"));
    assert!(!has("x", "d") && !has("x", "f") && !has("b", "y"));
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

#[test]
fn one_index_handles_several_complex_roles_and_uncertain_aliases() {
    let ontology = load(
        "TransitiveObjectProperty(:r) TransitiveObjectProperty(:s)
        SubObjectPropertyOf(ObjectPropertyChain(:p :q) :t)
        ObjectPropertyAssertion(:r :a :b) ObjectPropertyAssertion(:r :b :c)
        ObjectPropertyAssertion(:s :c :b) ObjectPropertyAssertion(:s :b :a)
        ObjectPropertyAssertion(:q :b :c)
        ClassAssertion(ObjectUnionOf(ObjectHasValue(:p :b) ObjectHasValue(:u :b)) :a)
        SubObjectPropertyOf(:u :p) SameIndividual(:c :cc)
        ClassAssertion(ObjectOneOf(:a :b) :x)",
    );
    let b = Build::new_arc();
    let individuals: Vec<_> = ["a", "b", "c", "cc", "x"]
        .iter()
        .map(|name| b.named_individual(format!("http://ex/{name}")))
        .collect();
    let mut index = ObjectPropertyInstanceIndex::new(&ontology).unwrap();
    for property in index.object_properties() {
        for ope in [
            OPE::ObjectProperty(property.clone()),
            OPE::InverseObjectProperty(property),
        ] {
            let mut expected = HashSet::new();
            for from in &individuals {
                for to in &individuals {
                    let assertion = ObjectPropertyAssertion {
                        ope: ope.clone(),
                        from: Individual::Named(from.clone()),
                        to: Individual::Named(to.clone()),
                    };
                    if is_entailed(&ontology, &assertion.into()).unwrap() {
                        expected.insert((from.clone(), to.clone()));
                    }
                }
            }
            assert_eq!(
                index.object_property_instances(ope.clone()).unwrap(),
                expected,
                "{ope:?}"
            );
            assert_eq!(index.object_property_instances(ope).unwrap(), expected);
        }
    }
}

#[test]
fn cached_property_queries_follow_tbox_changes() {
    let b = Build::new_arc();
    let p = b.object_property("http://ex/p");
    let r = OPE::ObjectProperty(b.object_property("http://ex/r"));
    let mut reasoner = IncrementalReasoner::new(load("ObjectPropertyAssertion(:p :a :b)"));
    assert!(reasoner
        .object_property_instances(r.clone())
        .unwrap()
        .is_empty());
    reasoner.add_axiom(
        horned_owl::model::SubObjectPropertyOf {
            sub: horned_owl::model::SubObjectPropertyExpression::ObjectPropertyExpression(
                OPE::ObjectProperty(p),
            ),
            sup: r.clone(),
        }
        .into(),
    );
    assert!(reasoner
        .object_property_instances(r.clone())
        .unwrap()
        .is_empty());
    reasoner.flush();
    assert_eq!(reasoner.object_property_instances(r).unwrap().len(), 1);
    assert_eq!(reasoner.last_flush_was_incremental(), Some(false));
}

#[test]
fn index_respects_inconsistency_and_fresh_entity_configuration() {
    let b = Build::new_arc();
    let r = OPE::ObjectProperty(b.object_property("http://ex/fresh"));
    let ontology = load("ClassAssertion(owl:Nothing :a) Declaration(NamedIndividual(:b))");
    let config = hermit_rs::configuration::Configuration {
        throw_inconsistent_ontology_exception: false,
        ..Default::default()
    };
    let mut index = ObjectPropertyInstanceIndex::with_configuration(&ontology, &config).unwrap();
    assert_eq!(index.object_property_instances(r.clone()).unwrap().len(), 4);
    let config = hermit_rs::configuration::Configuration {
        fresh_entity_policy: hermit_rs::configuration::FreshEntityPolicy::Disallow,
        ..Default::default()
    };
    let mut index = ObjectPropertyInstanceIndex::with_configuration(&load(""), &config).unwrap();
    assert!(index
        .object_property_instances(r)
        .unwrap_err()
        .starts_with("FreshEntitiesException"));
}

#[test]
fn complex_role_read_off_keeps_generated_edges_and_anonymous_paths() {
    for body in [
        "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)
         ClassAssertion(ObjectSomeValuesFrom(:p ObjectHasValue(:q :b)) :a)",
        "SubObjectPropertyOf(ObjectPropertyChain(:p :q) ObjectInverseOf(:r))
         ClassAssertion(ObjectSomeValuesFrom(:p ObjectHasValue(:q :b)) :a)",
        "SubObjectPropertyOf(ObjectPropertyChain(:p :p) :r)
         ClassAssertion(ObjectHasSelf(:p) :a) Declaration(NamedIndividual(:b))",
        "SubObjectPropertyOf(ObjectPropertyChain(:p :p) :r)
         ReflexiveObjectProperty(:p) Declaration(NamedIndividual(:a))
         Declaration(NamedIndividual(:b))",
        "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)
         ClassAssertion(ObjectUnionOf(ObjectHasValue(:r :b)
             ObjectSomeValuesFrom(:p ObjectHasValue(:q :b))) :a)",
        "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)
         SubClassOf(owl:Thing ObjectSomeValuesFrom(:p ObjectHasValue(:q :b)))
         Declaration(NamedIndividual(:a))",
    ] {
        check_against_oracle(body, &["a", "b"], "http://ex/r");
    }
}
