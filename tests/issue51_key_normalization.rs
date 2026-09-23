//! Issue #51: normalizing `HasKey(ObjectIntersectionOf(:A :B) (:r) (:dp))`.
//!
//! OWL 2 Structural Specification §9.5 gives `HasKey(CE (OPE1 ... OPEm) (DPE1
//! ... DPEn))` separate object and data property lists, and OWL 2 Direct
//! Semantics §2.3.5 identifies two named instances of CE that agree on *every*
//! listed property. So the normalized key must keep `:dp`, and its replacement
//! class K must contain CE (CE ⊑ K), because the key clause tests K in its body.
//!
//! The pinned `NormalizationTest.testKeys2` controls drop `:dp` (and fail in
//! Java, whose normalization keeps it). They also expect `D ⊑ A ⊓ B` with a key
//! on D, which is Java's normalization: nothing forces an individual into D, so
//! the key never fires. The port instead keys a class containing `A ⊓ B`;
//! `tests/java/corrections.json` documents the corrected replay oracle. These
//! checks establish the corrected result without that trace.
use hermit_rs::reasoner;
use hermit_rs::structural::{ClassExpr as CE, OWLAxioms, OWLNormalization, A};
use horned_owl::model::{ObjectPropertyExpression as OPE, PropertyExpression as PE};
use horned_owl::ontology::set::SetOntology;

fn read(axioms: &str) -> SetOntology<A> {
    let source = format!("Prefix(:=<urn:issue51:>)\nOntology(\n{axioms}\n)");
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
        .unwrap()
        .0
}

const KEY: &str = "Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
Declaration(DataProperty(:dp))
HasKey(ObjectIntersectionOf(:A :B) (:r) (:dp))";

fn name(ce: &CE) -> String {
    match ce {
        CE::Class(c) => c.0.to_string(),
        CE::ObjectComplementOf(inner) => format!("not {}", name(inner)),
        other => panic!("not a simple class expression: {other:?}"),
    }
}

#[test]
fn normalized_key_keeps_its_data_property_and_contains_its_class() {
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(&read(KEY)).unwrap();
    let axioms = normalization.into_axioms();
    assert_eq!(axioms.has_keys.len(), 1);
    let key = &axioms.has_keys[0];
    let properties: Vec<String> = key
        .property_expressions
        .iter()
        .map(|pe| match pe {
            PE::ObjectPropertyExpression(OPE::ObjectProperty(op)) => format!("object {}", &*op.0),
            PE::DataProperty(dp) => format!("data {}", &*dp.0),
            other => panic!("unexpected key property {other:?}"),
        })
        .collect();
    assert_eq!(properties, ["object urn:issue51:r", "data urn:issue51:dp"]);
    // owl:Thing ⊑ K ⊔ ¬A ⊔ ¬B, that is, A ⊓ B ⊑ K.
    assert_eq!(name(&key.class_expression), "internal:def#0");
    let mut inclusions: Vec<Vec<String>> = axioms
        .concept_inclusions
        .iter()
        .map(|inclusion| {
            let mut names: Vec<_> = inclusion.iter().map(name).collect();
            names.sort();
            names
        })
        .collect();
    inclusions.sort();
    assert_eq!(
        inclusions,
        [["internal:def#0", "not urn:issue51:A", "not urn:issue51:B"]]
    );
}

/// Two distinct named `A ⊓ B` instances with the same `:r` value.
fn abox(y_value: &str) -> String {
    format!(
        r#"{KEY}
Declaration(NamedIndividual(:x))
Declaration(NamedIndividual(:y))
Declaration(NamedIndividual(:z))
ClassAssertion(:A :x) ClassAssertion(:B :x)
ClassAssertion(:A :y) ClassAssertion(:B :y)
ObjectPropertyAssertion(:r :x :z) ObjectPropertyAssertion(:r :y :z)
DataPropertyAssertion(:dp :x "1"^^<http://www.w3.org/2001/XMLSchema#integer>)
DataPropertyAssertion(:dp :y "{y_value}"^^<http://www.w3.org/2001/XMLSchema#integer>)
DifferentIndividuals(:x :y)"#
    )
}

/// Different `:dp` values: the individuals do not agree on the whole key, so
/// they need not be equal. A key that lost `:dp` would identify them.
#[test]
fn key_requires_agreement_on_the_data_property() {
    assert!(reasoner::is_ontology_consistent(&read(&abox("2"))).unwrap());
}

/// Agreement on both properties identifies the two `A ⊓ B` instances, which
/// contradicts `DifferentIndividuals`. Java's normalization keys a class
/// contained in `A ⊓ B` that nothing populates; the faithful port of it found
/// this ontology consistent.
#[test]
fn key_applies_to_instances_of_the_complex_class() {
    assert!(!reasoner::is_ontology_consistent(&read(&abox("1"))).unwrap());
    // The same key on a named class, for comparison.
    let named = abox("1").replace("ObjectIntersectionOf(:A :B)", ":A");
    assert!(!reasoner::is_ontology_consistent(&read(&named)).unwrap());
}
