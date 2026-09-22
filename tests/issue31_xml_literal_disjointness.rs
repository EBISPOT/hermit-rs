//! Issue #31: rdf:XMLLiteral is disjoint from the other datatypes of the OWL 2
//! datatype map. OWL 2 Structural Specification §4.8 takes rdf:XMLLiteral from
//! RDF Concepts §5.1, whose XML values are disjoint from the value space of every
//! XML Schema datatype and from the strings. owl:real, owl:rational and
//! rdf:PlainLiteral hold numbers, strings and pairs of a string and a language
//! tag (OWL 2 §4.1, rdf:PlainLiteral §3), none of them an XML value. So no value
//! is both an XML literal and a value of another datatype, while the complement
//! of another datatype within the data domain (`DataComplementOf`, OWL 2 Direct
//! Semantics, Table 3) holds every XML literal. rdfs:Literal is the data domain.
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

/// Consistency of an ontology with the given axioms.
fn consistent_ontology(axioms: &str) -> bool {
    let source = format!(
        r#"Prefix(:=<urn:issue31:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)
Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
{axioms}
)"#
    );
    let ontology: SetOntology<A> =
        horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
            .unwrap()
            .0;
    reasoner::is_ontology_consistent(&ontology).unwrap()
}

/// Consistency of an ontology where `a` has at least `n` `dp` values, and every
/// `dp` value of `a` lies in each of `ranges`.
fn consistent(n: usize, ranges: &[&str]) -> bool {
    let ranges: String = ranges
        .iter()
        .map(|range| format!("SubClassOf(:A DataAllValuesFrom(:dp {range}))\n"))
        .collect();
    consistent_ontology(&format!(
        "ClassAssertion(:A :a)\nSubClassOf(:A DataMinCardinality({n} :dp))\n{ranges}"
    ))
}

/// Consistency of an ontology where `value` is a `dp` value of `a`, and every
/// `dp` value of `a` lies in `range`.
fn value_in(value: &str, range: &str) -> bool {
    consistent_ontology(&format!(
        "DataPropertyAssertion(:dp :a {value})\nClassAssertion(DataAllValuesFrom(:dp {range}) :a)"
    ))
}

/// Datatypes of the OWL 2 datatype map other than rdf:XMLLiteral: every other
/// value-space family, and subtypes within the families.
const OTHERS: &[&str] = &[
    "xsd:boolean",
    "rdf:PlainLiteral",
    "xsd:string",
    "xsd:NCName",
    "owl:real",
    "owl:rational",
    "xsd:decimal",
    "xsd:integer",
    "xsd:byte",
    "xsd:float",
    "xsd:double",
    "xsd:dateTime",
    "xsd:dateTimeStamp",
    "xsd:anyURI",
    "xsd:hexBinary",
    "xsd:base64Binary",
];

#[test]
fn no_fresh_value_is_an_xml_literal_and_a_value_of_another_datatype() {
    // XMLLiteralTest.testRange_3: rdf:XMLLiteral and xsd:boolean share no value.
    for other in OTHERS {
        assert!(!consistent(1, &["rdf:XMLLiteral", other]), "rdf:XMLLiteral and {other}");
        assert!(!consistent(1, &[other, "rdf:XMLLiteral"]), "{other} and rdf:XMLLiteral");
        let both = format!("DataIntersectionOf(rdf:XMLLiteral {other})");
        assert!(!consistent(1, &[&both]), "{both}");
        // The empty range is harmless when no value is required.
        assert!(consistent(0, &["rdf:XMLLiteral", other]), "no value in rdf:XMLLiteral and {other}");
    }
    // The ranges may come from different axioms.
    assert!(!consistent_ontology(
        "DataPropertyRange(:dp rdf:XMLLiteral)\nClassAssertion(DataSomeValuesFrom(:dp xsd:boolean) :a)"
    ));
    // A union with a disjoint datatype holds only its other members.
    assert!(!consistent(1, &["DataUnionOf(xsd:boolean xsd:string)", "rdf:XMLLiteral"]));
    assert!(consistent(5, &["DataUnionOf(xsd:boolean rdf:XMLLiteral)", "DataComplementOf(xsd:boolean)"]));
}

#[test]
fn complements_hold_the_values_outside_within_the_data_domain() {
    for other in OTHERS {
        // The complement of another datatype holds every XML literal, infinitely
        // many, and the complement of rdf:XMLLiteral holds the other datatype.
        let outside = format!("DataComplementOf({other})");
        assert!(consistent(5, &["rdf:XMLLiteral", &outside]), "rdf:XMLLiteral outside {other}");
        assert!(consistent(1, &[other, "DataComplementOf(rdf:XMLLiteral)"]), "{other} outside rdf:XMLLiteral");
    }
    assert!(!consistent(1, &["rdf:XMLLiteral", "DataComplementOf(rdf:XMLLiteral)"]));
    // Both booleans lie outside rdf:XMLLiteral, and nothing else is a boolean.
    assert!(consistent(2, &["xsd:boolean", "DataComplementOf(rdf:XMLLiteral)"]));
    assert!(!consistent(3, &["xsd:boolean", "DataComplementOf(rdf:XMLLiteral)"]));
    // Excluding some values leaves infinitely many XML literals.
    let excluded = r#"DataComplementOf(DataOneOf("<a/>"^^rdf:XMLLiteral "<b/>"^^rdf:XMLLiteral "true"^^xsd:boolean))"#;
    assert!(consistent(5, &["rdf:XMLLiteral", excluded]));
}

#[test]
fn rdfs_literal_is_the_data_domain() {
    assert!(consistent(3, &["rdf:XMLLiteral", "rdfs:Literal"]));
    assert!(consistent(3, &["rdfs:Literal", "DataComplementOf(rdf:XMLLiteral)"]));
    assert!(!consistent(1, &["rdf:XMLLiteral", "DataComplementOf(rdfs:Literal)"]));
}

#[test]
fn a_fixed_value_is_an_xml_literal_or_a_value_of_another_datatype() {
    let xml = r#""<a>b</a>"^^rdf:XMLLiteral"#;
    assert!(value_in(xml, "rdf:XMLLiteral"));
    assert!(value_in(xml, "rdfs:Literal"));
    assert!(!value_in(xml, "DataComplementOf(rdf:XMLLiteral)"));
    for other in OTHERS {
        assert!(!value_in(xml, other), "an XML literal in {other}");
        assert!(value_in(xml, &format!("DataComplementOf({other})")), "an XML literal outside {other}");
    }
    let others = [
        r#""true"^^xsd:boolean"#,
        r#""<a>b</a>""#,
        r#""<a>b</a>"@en"#,
        r#""<a>b</a>"^^xsd:string"#,
        r#""1"^^xsd:integer"#,
        r#""1.5"^^xsd:float"#,
        r#""2020-01-01T00:00:00Z"^^xsd:dateTime"#,
        r#""urn:a"^^xsd:anyURI"#,
        r#""0A"^^xsd:hexBinary"#,
    ];
    for value in others {
        assert!(!value_in(value, "rdf:XMLLiteral"), "{value} in rdf:XMLLiteral");
        assert!(value_in(value, "DataComplementOf(rdf:XMLLiteral)"), "{value} outside rdf:XMLLiteral");
    }
    // An enumeration holds the XML literals it names and nothing else of
    // rdf:XMLLiteral: here one XML literal, a boolean and a string.
    let mixed = r#"DataOneOf("<a/>"^^rdf:XMLLiteral "true"^^xsd:boolean "<a/>")"#;
    assert!(consistent(1, &[mixed, "rdf:XMLLiteral"]));
    assert!(!consistent(2, &[mixed, "rdf:XMLLiteral"]));
    assert!(consistent(2, &[mixed, "DataComplementOf(rdf:XMLLiteral)"]));
    assert!(!consistent(3, &[mixed, "DataComplementOf(rdf:XMLLiteral)"]));
    // The XML literal whose content is the text "b" is not the string "b".
    let functional = |second: &str| {
        consistent_ontology(&format!(
            "FunctionalDataProperty(:dp)\nDataPropertyAssertion(:dp :a \"b\"^^rdf:XMLLiteral)\n\
             DataPropertyAssertion(:dp :a {second})"
        ))
    };
    assert!(functional(r#""b"^^rdf:XMLLiteral"#));
    assert!(!functional(r#""b"^^xsd:string"#));
    assert!(!functional(r#""b""#));
}

#[test]
fn a_defined_datatype_has_the_value_space_of_its_definition() {
    // DatatypeDefinition makes :text a name for xsd:string and :xml a name for
    // rdf:XMLLiteral (OWL 2 Structural Specification §9.4).
    let defined = |n: usize, ranges: &[&str]| {
        let ranges: String = ranges
            .iter()
            .map(|range| format!("SubClassOf(:A DataAllValuesFrom(:dp {range}))\n"))
            .collect();
        consistent_ontology(&format!(
            "Declaration(Datatype(:text))\nDatatypeDefinition(:text xsd:string)\n\
             Declaration(Datatype(:xml))\nDatatypeDefinition(:xml rdf:XMLLiteral)\n\
             ClassAssertion(:A :a)\nSubClassOf(:A DataMinCardinality({n} :dp))\n{ranges}"
        ))
    };
    assert!(!defined(1, &[":text", "rdf:XMLLiteral"]));
    assert!(!defined(1, &[":xml", "xsd:boolean"]));
    assert!(!defined(1, &[":xml", ":text"]));
    assert!(defined(3, &[":xml", "DataComplementOf(:text)"]));
    assert!(defined(3, &[":xml", "rdf:XMLLiteral"]));
}
