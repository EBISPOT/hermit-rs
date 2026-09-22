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
