//! A `xsd:base64Binary` literal denotes a base64Binary value. XSD 1.1 Part 2
//! §3.3.16 gives base64Binary a value space of finite octet sequences, and
//! OWL 2 Structural Specification §4.6 (Binary Data) states that the value
//! spaces of `xsd:hexBinary` and `xsd:base64Binary` are disjoint. So
//! `"QQ=="^^xsd:base64Binary` (the single octet 0x41) lies in
//! `xsd:base64Binary` and not in `xsd:hexBinary`, and it differs from
//! `"41"^^xsd:hexBinary` although both encode the same octets. Two base64
//! literals decoding to the same octets (`"QQ=="` and `"Q Q = ="`) denote one
//! value.
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

fn consistent(axioms: &str) -> bool {
    let source = format!(
        r#"Prefix(:=<urn:base64-binary:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)
Ontology(
Declaration(NamedIndividual(:a))
Declaration(DataProperty(:dp))
Declaration(DataProperty(:dq))
{axioms}
)"#
    );
    let ontology: SetOntology<A> =
        horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
            .unwrap()
            .0;
    reasoner::is_ontology_consistent(&ontology).unwrap()
}

/// `a` has `value` for `dp`, and every `dp` value lies in `range`.
fn value_in_range(value: &str, range: &str) -> bool {
    consistent(&format!("DataPropertyRange(:dp {range})\nDataPropertyAssertion(:dp :a {value})"))
}

const BASE64: &str = r#""QQ=="^^xsd:base64Binary"#;
const HEX: &str = r#""41"^^xsd:hexBinary"#;

#[test]
fn base64_literal_is_a_base64_value_and_not_a_hex_value() {
    assert!(value_in_range(BASE64, "xsd:base64Binary"));
    assert!(!value_in_range(BASE64, "xsd:hexBinary"));
    assert!(value_in_range(HEX, "xsd:hexBinary"));
    assert!(!value_in_range(HEX, "xsd:base64Binary"));
    // The empty octet sequence too: "" of each datatype is its own value.
    assert!(value_in_range(r#"""^^xsd:base64Binary"#, "xsd:base64Binary"));
    assert!(!value_in_range(r#"""^^xsd:base64Binary"#, "xsd:hexBinary"));
}

#[test]
fn base64_length_facets_count_octets() {
    let length = |n: &str| format!(r#"DatatypeRestriction(xsd:base64Binary xsd:length "{n}"^^xsd:integer)"#);
    assert!(value_in_range(BASE64, &length("1")));
    assert!(!value_in_range(BASE64, &length("2")));
    assert!(value_in_range(r#""QUJD"^^xsd:base64Binary"#, &length("3")));
    // A hexBinary length restriction admits no base64Binary value.
    assert!(!value_in_range(
        BASE64,
        r#"DatatypeRestriction(xsd:hexBinary xsd:length "1"^^xsd:integer)"#
    ));
    // Outside base64Binary[maxLength 0], which is only the empty sequence.
    assert!(value_in_range(
        BASE64,
        r#"DataComplementOf(DatatypeRestriction(xsd:base64Binary xsd:maxLength "0"^^xsd:integer))"#
    ));
    assert!(!value_in_range(
        r#"""^^xsd:base64Binary"#,
        r#"DataComplementOf(DatatypeRestriction(xsd:base64Binary xsd:maxLength "0"^^xsd:integer))"#
    ));
}

#[test]
fn base64_literals_in_enumerations() {
    assert!(value_in_range(BASE64, r#"DataOneOf("Q Q = ="^^xsd:base64Binary)"#));
    assert!(!value_in_range(BASE64, &format!("DataOneOf({HEX})")));
    assert!(!value_in_range(HEX, &format!("DataOneOf({BASE64})")));
    // base64Binary[length 0] is {""^^base64Binary}; excluding it leaves nothing.
    assert!(!consistent(
        r#"ClassAssertion(DataSomeValuesFrom(:dp DataIntersectionOf(
    DatatypeRestriction(xsd:base64Binary xsd:length "0"^^xsd:integer)
    DataComplementOf(DataOneOf(""^^xsd:base64Binary)))) :a)"#
    ));
    // Excluding the hexBinary "" removes nothing from the base64Binary space.
    assert!(consistent(
        r#"ClassAssertion(DataSomeValuesFrom(:dp DataIntersectionOf(
    DatatypeRestriction(xsd:base64Binary xsd:length "0"^^xsd:integer)
    DataComplementOf(DataOneOf(""^^xsd:hexBinary)))) :a)"#
    ));
}

#[test]
fn base64_counting() {
    // base64Binary[length 0] holds one value, so two distinct ones do not fit,
    // while a hexBinary and a base64Binary empty sequence are two values.
    let empty = r#"DatatypeRestriction(xsd:base64Binary xsd:length "0"^^xsd:integer)"#;
    assert!(consistent(&format!("ClassAssertion(DataMinCardinality(1 :dp {empty}) :a)")));
    assert!(!consistent(&format!("ClassAssertion(DataMinCardinality(2 :dp {empty}) :a)")));
    assert!(consistent(
        r#"ClassAssertion(DataMinCardinality(2 :dp DataOneOf(""^^xsd:base64Binary ""^^xsd:hexBinary)) :a)"#
    ));
    assert!(!consistent(
        r#"ClassAssertion(DataMinCardinality(2 :dp DataOneOf("QQ=="^^xsd:base64Binary "Q Q = ="^^xsd:base64Binary)) :a)"#
    ));
    assert!(consistent(&format!(
        "ClassAssertion(DataMinCardinality(2 :dp DataOneOf({BASE64} {HEX})) :a)"
    )));
}

#[test]
fn base64_and_hex_constants_are_different_values() {
    let negative = |positive: &str, negative: &str| {
        consistent(&format!(
            "DataPropertyAssertion(:dp :a {positive})\nNegativeDataPropertyAssertion(:dp :a {negative})"
        ))
    };
    let disjoint = |first: &str, second: &str| {
        consistent(&format!(
            "DisjointDataProperties(:dp :dq)\nDataPropertyAssertion(:dp :a {first})\nDataPropertyAssertion(:dq :a {second})"
        ))
    };
    assert!(negative(BASE64, HEX));
    assert!(negative(HEX, BASE64));
    assert!(disjoint(BASE64, HEX));
    // Two base64 spellings of the octet 0x41 are one value.
    assert!(!negative(BASE64, r#""Q Q = ="^^xsd:base64Binary"#));
    assert!(!disjoint(BASE64, r#""Q Q = ="^^xsd:base64Binary"#));
    // A functional property merges its values only when they are equal.
    let functional = |first: &str, second: &str| {
        consistent(&format!(
            "FunctionalDataProperty(:dp)\nDataPropertyAssertion(:dp :a {first})\nDataPropertyAssertion(:dp :a {second})"
        ))
    };
    assert!(!functional(BASE64, HEX));
    assert!(functional(BASE64, r#""Q Q = ="^^xsd:base64Binary"#));
}
