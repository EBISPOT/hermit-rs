use hermit_rs::{reasoner, structural::A};
use horned_owl::{model::*, ontology::set::SetOntology};
fn parse(s: &str) -> SetOntology<A> {
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(s), Default::default())
        .unwrap()
        .0
}
const MINIMAL: &str = include_str!("fixtures/issue8/minimal.ofn");
#[test]
fn ro_import_minimal_is_consistent() {
    assert!(reasoner::is_ontology_consistent(&parse(MINIMAL)).unwrap());
}
#[test]
fn ro_import_consistency_is_independent_of_axiom_order() {
    let lines: Vec<_> = MINIMAL.lines().collect();
    let axioms = &lines[2..lines.len() - 1];
    for reverse in [false, true] {
        for offset in 0..axioms.len() {
            let mut ordered = axioms.to_vec();
            ordered.rotate_left(offset);
            if reverse {
                ordered.reverse();
            }
            let input = format!("{}\n{}\n{}\n)", lines[0], lines[1], ordered.join("\n"));
            assert!(
                reasoner::is_ontology_consistent(&parse(&input)).unwrap(),
                "reverse={reverse}, offset={offset}"
            );
        }
    }
}
#[test]
fn chain_prefix_does_not_imply_its_superproperty() {
    let o = parse(MINIMAL);
    let b = Build::new_arc();
    let a = b.named_individual("http://purl.obolibrary.org/obo/ENVO_01001600");
    let c = b.named_individual("http://purl.obolibrary.org/obo/ENVO_01001583");
    let q = ObjectPropertyExpression::ObjectProperty(
        b.object_property("http://purl.obolibrary.org/obo/RO_0000056"),
    );
    assert!(!reasoner::has_object_property_relationship(&o, &a, q.clone(), &c).unwrap());
    assert!(!reasoner::has_object_property_relationship(&o, &c, q, &a).unwrap());
}
#[test]
fn inconsistent_ontology_has_a_minimal_explanation() {
    let o=parse("Prefix(:=<urn:test:>) Prefix(owl:=<http://www.w3.org/2002/07/owl#>) Ontology(Declaration(Class(:Unused)) ClassAssertion(:A :a) ClassAssertion(ObjectComplementOf(:A) :a))");
    let b = Build::new_arc();
    let contradiction: Component<A> = SubClassOf {
        sub: ClassExpression::Class(b.class("http://www.w3.org/2002/07/owl#Thing")),
        sup: ClassExpression::Class(b.class("http://www.w3.org/2002/07/owl#Nothing")),
    }
    .into();
    let support = reasoner::explain(&o, &contradiction)
        .unwrap()
        .expect("inconsistency justification");
    assert_eq!(support.len(), 2);
    for omitted in 0..support.len() {
        let mut reduced = SetOntology::new();
        for (i, axiom) in support.iter().enumerate() {
            if i != omitted {
                reduced.insert(axiom.clone());
            }
        }
        assert!(reasoner::is_ontology_consistent(&reduced).unwrap());
    }
}
#[test]
fn ro_import_consistency_is_independent_of_role_names() {
    for seed in 0..32 {
        let mut text = MINIMAL.to_string();
        for (index, old) in ["BFO_0000050", "BFO_0000051", "RO_0000056", "RO_0000057"]
            .iter()
            .enumerate()
        {
            text = text.replace(old, &format!("role_{seed}_{index}"));
        }
        assert!(
            reasoner::is_ontology_consistent(&parse(&text)).unwrap(),
            "renaming {seed}"
        );
    }
}
#[test]
fn inverse_transitive_chain_still_entails_complete_paths() {
    let mut o = parse(MINIMAL);
    let b = Build::new_arc();
    let named = |s: &str| b.named_individual(format!("http://purl.obolibrary.org/obo/{s}"));
    let property = |s: &str| {
        ObjectPropertyExpression::ObjectProperty(
            b.object_property(format!("http://purl.obolibrary.org/obo/{s}")),
        )
    };
    let a = named("ENVO_01001600");
    let b_ind = named("ENVO_01001583");
    let parent = named("parent");
    let participant = named("participant");
    o.insert(ObjectPropertyAssertion {
        ope: property("BFO_0000050"),
        from: Individual::Named(b_ind.clone()),
        to: Individual::Named(parent.clone()),
    });
    o.insert(ObjectPropertyAssertion {
        ope: property("RO_0000057"),
        from: Individual::Named(a),
        to: Individual::Named(participant.clone()),
    });
    assert!(reasoner::is_ontology_consistent(&o).unwrap());
    for subject in [b_ind, parent] {
        assert!(reasoner::has_object_property_relationship(
            &o,
            &subject,
            property("RO_0000057"),
            &participant
        )
        .unwrap());
    }
}
#[test]
fn ro_import_consistency_is_independent_of_shuffled_axiom_order() {
    let lines: Vec<_> = MINIMAL.lines().collect();
    let axioms = &lines[2..lines.len() - 1];
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    for seed in 0..64 {
        let mut ordered = axioms.to_vec();
        for i in (1..ordered.len()).rev() {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            ordered.swap(i, ((state >> 33) as usize) % (i + 1));
        }
        let mut input = format!("{}\n{}\n{}\n)", lines[0], lines[1], ordered.join("\n"));
        if seed % 2 == 1 {
            for (index, old) in ["BFO_0000050", "BFO_0000051", "RO_0000056", "RO_0000057"]
                .iter()
                .enumerate()
            {
                input = input.replace(old, &format!("shuffled_{}_{index}", (seed * 5 + index) % 7));
            }
        }
        assert!(
            reasoner::is_ontology_consistent(&parse(&input)).unwrap(),
            "seed={seed}: {ordered:?}"
        );
    }
}
/// The second half of issue #8: an inconsistency that only arises through the
/// inverse-transitive chain must still be explainable. As in Java HermiT with
/// `throwInconsistentOntologyException=false` under the OWL API's black-box
/// explanation, the justification of `owl:Thing ⊑ owl:Nothing` is the explanation of
/// the inconsistency; the public entailment query keeps throwing by default.
#[test]
fn chain_dependent_inconsistency_is_explained_not_rejected() {
    use hermit_rs::configuration::Configuration;
    use std::collections::BTreeSet;
    let text = MINIMAL.replace(
        "\n)",
        "\nClassAssertion(obo:BFO_0000002 obo:ENVO_01001600)\n\
         ClassAssertion(ObjectSomeValuesFrom(obo:RO_0000057 owl:Thing) obo:ENVO_01001600)\n)",
    );
    let text = format!("Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n{text}");
    let o = parse(&text);
    assert!(!reasoner::is_ontology_consistent(&o).unwrap());
    let b = Build::new_arc();
    let class = |s: &str| ClassExpression::Class(b.class(s));
    let contradiction: Component<A> = SubClassOf {
        sub: class("http://www.w3.org/2002/07/owl#Thing"),
        sup: class("http://www.w3.org/2002/07/owl#Nothing"),
    }
    .into();
    let unrelated: Component<A> = SubClassOf {
        sub: class("urn:test:X"),
        sup: class("urn:test:Y"),
    }
    .into();

    // Default public queries keep Java's InconsistentOntologyException contract.
    assert_eq!(
        reasoner::is_entailed(&o, &contradiction),
        Err(reasoner::INCONSISTENT_ONTOLOGY_ERROR.to_string())
    );
    // With the throw disabled, an inconsistent ontology entails everything.
    let configuration = Configuration {
        throw_inconsistent_ontology_exception: false,
        ..Default::default()
    };
    let mut lenient = reasoner::IncrementalReasoner::with_configuration(o.clone(), configuration);
    assert!(lenient.is_entailed(&contradiction).unwrap());
    assert!(lenient.is_entailed(&unrelated).unwrap());

    // Everything except the transitivity and the domain axiom is needed.
    let expected: BTreeSet<Component<A>> = o
        .iter()
        .map(|ac| ac.component.clone())
        .filter(|c| {
            !matches!(
                c,
                Component::TransitiveObjectProperty(_)
                    | Component::ObjectPropertyDomain(_)
                    | Component::OntologyID(_)
                    | Component::DocIRI(_)
            )
        })
        .collect();
    assert_eq!(expected.len(), 8);
    let support = reasoner::explain(&o, &contradiction)
        .unwrap()
        .expect("inconsistency justification");
    assert_eq!(support.iter().cloned().collect::<BTreeSet<_>>(), expected);
    let all = reasoner::all_explanations(&o, &contradiction).unwrap();
    assert_eq!(all.len(), 1);
    assert_eq!(all[0].iter().cloned().collect::<BTreeSet<_>>(), expected);
    // Any axiom is entailed by an inconsistent ontology; its justification is the
    // inconsistency itself.
    let support = reasoner::explain(&o, &unrelated)
        .unwrap()
        .expect("justification");
    assert_eq!(support.into_iter().collect::<BTreeSet<_>>(), expected);
}
