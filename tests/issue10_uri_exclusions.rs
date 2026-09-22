//! Issues #10 and #11: values excluded by `DataComplementOf(DataOneOf(...))` are
//! removed from a finite `xsd:anyURI` value space, including one that is finite
//! only because a length window, or the complement of a length restriction,
//! bounds an infinite pattern. An anyURI value is its character sequence (XSD 1.1
//! Part 2 §3.3.17), and the anyURI and string value spaces are disjoint (OWL 2
//! Structural Specification §4.6), so a string literal excludes no anyURI value.
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
        r#"Prefix(:=<urn:issue10:>)
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

/// `ab(c+)` with lengths 4..5: exactly {abcc, abccc} (issue #10).
const WINDOW: &str = r#"DatatypeRestriction(xsd:anyURI xsd:pattern "ab(c+)"^^xsd:string xsd:minLength "4"^^xsd:integer xsd:maxLength "5"^^xsd:integer)"#;
/// With `SHORTER_THAN_5`, `ab(c*)` is exactly {ab, abc, abcc} (issue #11).
const PATTERN: &str = r#"DatatypeRestriction(xsd:anyURI xsd:pattern "ab(c*)"^^xsd:string)"#;
const SHORTER_THAN_5: &str =
    r#"DataComplementOf(DatatypeRestriction(xsd:anyURI xsd:minLength "5"^^xsd:integer))"#;

fn excluding(literals: &str) -> String {
    format!("DataComplementOf(DataOneOf({literals}))")
}

#[test]
fn excluding_every_value_empties_the_range() {
    let window_values = excluding(r#""abcc"^^xsd:anyURI "abccc"^^xsd:anyURI"#);
    assert!(!consistent(&[WINDOW, window_values.as_str()], ""));
    let short_values = excluding(r#""ab"^^xsd:anyURI "abc"^^xsd:anyURI "abcc"^^xsd:anyURI"#);
    assert!(!consistent(&[PATTERN, SHORTER_THAN_5, short_values.as_str()], ""));
    // The issue #9 range is exactly {""^^xsd:anyURI}.
    let empty_uri = excluding(r#"""^^xsd:anyURI"#);
    assert!(!consistent(
        &[
            r#"DatatypeRestriction(xsd:anyURI xsd:minLength "0"^^xsd:integer)"#,
            r#"DataComplementOf(DatatypeRestriction(xsd:anyURI xsd:minLength "1"^^xsd:integer))"#,
            empty_uri.as_str(),
        ],
        "",
    ));
}

#[test]
fn values_that_are_not_excluded_remain() {
    // Only abccc remains, so a has one dp value and it is abccc.
    let abcc = excluding(r#""abcc"^^xsd:anyURI"#);
    let one_left = [WINDOW, abcc.as_str()];
    assert!(consistent(&one_left, ""));
    assert!(consistent(&one_left, r#"DataPropertyAssertion(:dp :a "abccc"^^xsd:anyURI)"#));
    assert!(!consistent(&one_left, r#"DataPropertyAssertion(:dp :a "abcc"^^xsd:anyURI)"#));
    assert!(!consistent(&one_left, "SubClassOf(:A DataMinCardinality(2 :dp))"));
    // ab and abcc remain.
    let abc = excluding(r#""abc"^^xsd:anyURI"#);
    let two_left = [PATTERN, SHORTER_THAN_5, abc.as_str()];
    assert!(consistent(&two_left, "SubClassOf(:A DataMinCardinality(2 :dp))"));
    assert!(!consistent(&two_left, "SubClassOf(:A DataMinCardinality(3 :dp))"));
    // Strings are not anyURI values, so both anyURI values remain.
    let strings = excluding(r#""abcc"^^xsd:string "abccc"^^xsd:string"#);
    let both_left = [WINDOW, strings.as_str()];
    assert!(consistent(&both_left, "SubClassOf(:A DataMinCardinality(2 :dp))"));
    assert!(!consistent(&both_left, "SubClassOf(:A DataMinCardinality(3 :dp))"));
}

#[test]
fn uris_beyond_the_string_alphabet_remain() {
    // [𐀀-𐀐a] denotes 18 anyURI values. Seventeen are supplementary-plane
    // characters, which the string automata cannot represent, so they must not
    // be lost when a is excluded.
    let wide = "DatatypeRestriction(xsd:anyURI xsd:pattern \"[\u{10000}-\u{10010}a]\"^^xsd:string)";
    let a = excluding(r#""a"^^xsd:anyURI"#);
    let seventeen_left = [wide, a.as_str()];
    assert!(consistent(&seventeen_left, "SubClassOf(:A DataMinCardinality(17 :dp))"));
    assert!(!consistent(&seventeen_left, "SubClassOf(:A DataMinCardinality(18 :dp))"));
}
