//! Issue #12: a negated binary length restriction is subtracted from the value
//! space. hexBinary values are finite octet sequences whose length counts octets
//! (XSD 1.1 Part 2 §3.3.15), and `DataComplementOf` is the complement within the
//! data domain (OWL 2 Direct Semantics, Table 3). So `xsd:hexBinary[minLength 0]`
//! outside `xsd:hexBinary[minLength 1]` is exactly the empty octet sequence.
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

/// Consistency of an ontology where `a` has a `dp` value, every `dp` value of
/// `a` lies in each of `ranges`, and `extra` holds.
fn consistent(ranges: &[&str], extra: &str) -> bool {
    let ranges: String = ranges
        .iter()
        .map(|range| format!("SubClassOf(:A DataAllValuesFrom(:dp {range}))\n"))
        .collect();
    let source = format!(
        r#"Prefix(:=<urn:issue12:>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
ClassAssertion(:A :a)
SubClassOf(:A DataMinCardinality(1 :dp))
{ranges}{extra}
)"#
    );
    let ontology: SetOntology<A> =
        horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
            .unwrap()
            .0;
    reasoner::is_ontology_consistent(&ontology).unwrap()
}

const ANY_LENGTH: &str = r#"DatatypeRestriction(xsd:hexBinary xsd:minLength "0"^^xsd:integer)"#;
const SHORTER_THAN_1: &str =
    r#"DataComplementOf(DatatypeRestriction(xsd:hexBinary xsd:minLength "1"^^xsd:integer))"#;

#[test]
fn only_the_empty_octet_sequence_remains() {
    let range = [ANY_LENGTH, SHORTER_THAN_1];
    assert!(consistent(&range, ""));
    assert!(consistent(&range, r#"DataPropertyAssertion(:dp :a ""^^xsd:hexBinary)"#));
    assert!(!consistent(&range, r#"DataPropertyAssertion(:dp :a "00"^^xsd:hexBinary)"#));
    assert!(!consistent(&range, "SubClassOf(:A DataMinCardinality(2 :dp))"));
    let without_it = r#"DataComplementOf(DataOneOf(""^^xsd:hexBinary))"#;
    assert!(!consistent(&[ANY_LENGTH, SHORTER_THAN_1, without_it], ""));
}

#[test]
fn subtracting_every_length_empties_the_range() {
    let nonempty = r#"DatatypeRestriction(xsd:hexBinary xsd:minLength "1"^^xsd:integer)"#;
    let no_length = r#"DataComplementOf(DatatypeRestriction(xsd:hexBinary xsd:minLength "0"^^xsd:integer))"#;
    assert!(!consistent(&[nonempty, no_length], ""));
}

#[test]
fn lengths_outside_the_subtracted_window_remain() {
    // Lengths 0..3 minus lengths 1..2 leave "" and the 256^3 sequences of length 3.
    let up_to_3 = r#"DatatypeRestriction(xsd:hexBinary xsd:maxLength "3"^^xsd:integer)"#;
    let not_1_to_2 = r#"DataComplementOf(DatatypeRestriction(xsd:hexBinary xsd:minLength "1"^^xsd:integer xsd:maxLength "2"^^xsd:integer))"#;
    let two_windows = [up_to_3, not_1_to_2];
    assert!(consistent(&two_windows, "SubClassOf(:A DataMinCardinality(3 :dp))"));
    assert!(consistent(&two_windows, r#"DataPropertyAssertion(:dp :a "0A0B0C"^^xsd:hexBinary)"#));
    assert!(!consistent(&two_windows, r#"DataPropertyAssertion(:dp :a "0A0B"^^xsd:hexBinary)"#));
    // base64Binary is disjoint from hexBinary, so its complement removes no
    // hexBinary value and "" remains.
    let not_empty_base64 =
        r#"DataComplementOf(DatatypeRestriction(xsd:base64Binary xsd:maxLength "0"^^xsd:integer))"#;
    assert!(consistent(&[ANY_LENGTH, SHORTER_THAN_1, not_empty_base64], ""));
}
