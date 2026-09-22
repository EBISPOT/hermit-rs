//! Issue #17: negated string restrictions and excluded values are subtracted
//! from the value space of rdf:PlainLiteral and the string datatypes. That
//! value space holds the strings and the pairs of a string and a lowercase
//! language tag (rdf:PlainLiteral §3); xsd:string holds the strings only.
//! `DataComplementOf` is the complement within the data domain (OWL 2 Direct
//! Semantics, Table 3).
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

/// Consistency of an ontology with the given axioms.
fn consistent_ontology(axioms: &str) -> bool {
    let source = format!(
        r#"Prefix(:=<urn:issue17:>)
Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)
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

fn excluding(members: &str) -> String {
    format!("DataComplementOf(DataOneOf({members}))")
}

#[test]
fn an_excluded_value_empties_the_empty_string_range() {
    // RDFPlainLiteralTest.testSize_3: xsd:string[length 0] holds only "".
    let empty_string = r#"DatatypeRestriction(xsd:string xsd:length "0"^^xsd:integer)"#;
    assert!(consistent(1, &[empty_string]));
    assert!(!consistent(2, &[empty_string]));
    assert!(!consistent(1, &[empty_string, &excluding(r#"""^^xsd:string"#)]));
    assert!(!consistent(1, &[empty_string, &excluding(r#""""#)]));
    assert!(consistent(1, &[empty_string, &excluding(r#""a" ""@en "0"^^xsd:integer"#)]));
    // rdf:PlainLiteral[length 0] also holds "" with any language tag.
    let empty_plain = r#"DatatypeRestriction(rdf:PlainLiteral xsd:length "0"^^xsd:integer)"#;
    assert!(consistent(3, &[empty_plain, &excluding(r#""" ""@en"#)]));
    let untagged = r#"DataComplementOf(DatatypeRestriction(rdf:PlainLiteral rdf:langRange "*"))"#;
    assert!(consistent(1, &[empty_plain, untagged]));
    assert!(!consistent(1, &[empty_plain, untagged, &excluding(r#""""#)]));
}

#[test]
fn negated_restrictions_are_subtracted() {
    // Lengths up to 1 less the strings of length 1 leave "".
    let short = [
        r#"DatatypeRestriction(xsd:string xsd:maxLength "1"^^xsd:integer)"#,
        r#"DataComplementOf(DatatypeRestriction(xsd:string xsd:minLength "1"^^xsd:integer))"#,
    ];
    assert!(consistent(1, &short));
    assert!(!consistent(2, &short));
    let mut none = short.to_vec();
    let empty = excluding(r#""""#);
    none.push(&empty);
    assert!(!consistent(1, &none));
    // No string has two lengths.
    assert!(!consistent(
        1,
        &[
            r#"DatatypeRestriction(xsd:string xsd:length "1"^^xsd:integer)"#,
            r#"DatatypeRestriction(xsd:string xsd:length "2"^^xsd:integer)"#,
            r#"DatatypeRestriction(xsd:string xsd:length "3"^^xsd:integer)"#,
        ]
    ));
    // A pattern: ab, abc and abcc, less abc.
    let pattern = [
        r#"DatatypeRestriction(xsd:string xsd:pattern "ab(c*)")"#,
        r#"DataComplementOf(DatatypeRestriction(xsd:string xsd:minLength "5"^^xsd:integer))"#,
    ];
    let without_abc = excluding(r#""abc""#);
    let mut two = pattern.to_vec();
    two.push(&without_abc);
    assert!(consistent(2, &two));
    assert!(!consistent(3, &two));
}

#[test]
fn plain_literals_hold_tagged_pairs() {
    // xsd:string is the part of rdf:PlainLiteral without tags.
    let plain = r#"DatatypeRestriction(rdf:PlainLiteral xsd:pattern "a")"#;
    assert!(consistent(5, &[plain]));
    assert!(!consistent(2, &[plain, "xsd:string"]));
    assert!(consistent(2, &[plain, "DataComplementOf(xsd:string)"]));
    assert!(!consistent(1, &["xsd:string", "DataComplementOf(rdf:PlainLiteral)"]));
    // A window of strings, one of tagged pairs and a pattern meet in "a", "aa", ...
    let windows = [
        r#"DatatypeRestriction(rdf:PlainLiteral xsd:minLength "1"^^xsd:integer)"#,
        r#"DatatypeRestriction(rdf:PlainLiteral xsd:pattern "a+")"#,
    ];
    assert!(consistent(3, &windows));
}

#[test]
fn language_tags_compare_case_insensitively() {
    // "x"@en and "x"@EN are one value, so a functional property may have both.
    let values = |second: &str| {
        format!(
            "FunctionalDataProperty(:dp)\nDataPropertyAssertion(:dp :a \"x\"@en)\n\
             DataPropertyAssertion(:dp :a {second})"
        )
    };
    assert!(consistent_ontology(&values("\"x\"@EN")));
    assert!(!consistent_ontology(&values("\"x\"@fr")));
    // Excluding "x"@EN excludes "x"@en, and a value space of rdf:langRange "EN"
    // holds it.
    let range = |range: &str| {
        consistent_ontology(&format!(
            "DataPropertyAssertion(:dp :a \"x\"@en)\nClassAssertion(DataAllValuesFrom(:dp {range}) :a)"
        ))
    };
    assert!(!range("DataComplementOf(DataOneOf(\"x\"@EN))"));
    assert!(range("DataComplementOf(DataOneOf(\"x\"@EN-GB))"));
    assert!(range("DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"EN\")"));
}

#[test]
fn lang_range_matches_by_extended_filtering() {
    // RFC 4647 §3.3.2, as rdf:PlainLiteral §3 requires: "de-1996" matches
    // de-DE-1996 (basic filtering does not), and "de-DE" does not match de-x-DE,
    // whose DE follows the singleton x.
    let tagged = |tag: &str, range: &str| {
        consistent_ontology(&format!(
            "DataPropertyAssertion(:dp :a \"x\"@{tag})\n\
             ClassAssertion(DataAllValuesFrom(:dp DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"{range}\")) :a)"
        ))
    };
    assert!(tagged("de-DE-1996", "de-1996"));
    assert!(tagged("de-DE-1996", "DE-de"));
    assert!(!tagged("de-x-DE", "de-DE"));
    assert!(!tagged("de-DE", "fr"));
}

#[test]
fn strings_hold_every_xml_character() {
    // #xD is an XML character, so the pattern \r and the four characters of \s
    // denote strings (XSD 1.1 Part 2 §3.3.1, §G.4.2.5).
    assert!(consistent(1, &[r#"DatatypeRestriction(xsd:string xsd:pattern "\\r")"#]));
    assert!(consistent(4, &[r#"DatatypeRestriction(xsd:string xsd:pattern "\\s")"#]));
    assert!(!consistent(5, &[r#"DatatypeRestriction(xsd:string xsd:pattern "\\s")"#]));
}

#[test]
fn length_only_restrictions_stay_windows() {
    // A restriction with length facets only is a length window, as in HermiT, so
    // a large bound costs nothing. Built as an automaton, this one never finished.
    assert!(consistent(2, &[r#"DatatypeRestriction(xsd:string xsd:maxLength "100000"^^xsd:integer)"#]));
}
