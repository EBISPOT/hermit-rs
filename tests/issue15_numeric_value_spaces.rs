//! Issues #15 and #16: negated numeric restrictions and excluded values are
//! subtracted from the numeric value space. owl:real, owl:rational, xsd:decimal
//! and the integer datatypes share one value space, whose values nest (OWL 2
//! Structural Specification §4.1); xsd:float and xsd:double each have their own
//! (§4.2). `DataComplementOf` is the complement within the data domain (OWL 2
//! Direct Semantics, Table 3).
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

/// Consistency of an ontology with the given axioms.
fn consistent_ontology(axioms: &str) -> bool {
    let source = format!(
        r#"Prefix(:=<urn:issue15:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
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

/// Consistency of an ontology where `a` has a `dp` value, every `dp` value of
/// `a` lies in each of `ranges`, and `extra` holds.
fn consistent(ranges: &[&str], extra: &str) -> bool {
    let ranges: String = ranges
        .iter()
        .map(|range| format!("SubClassOf(:A DataAllValuesFrom(:dp {range}))\n"))
        .collect();
    consistent_ontology(&format!(
        "ClassAssertion(:A :a)\nSubClassOf(:A DataMinCardinality(1 :dp))\n{ranges}{extra}"
    ))
}

/// `a` has `dp` values distinct from each of `values`, as in
/// `NumericsTest.assertDRSatisfiableNEQ`: `a` has each value for a property
/// disjoint with `dp`.
fn distinct_from(values: &[&str]) -> String {
    values
        .iter()
        .enumerate()
        .map(|(i, value)| {
            format!("DisjointDataProperties(:dp :v{i})\nDataPropertyAssertion(:v{i} :a {value})\n")
        })
        .collect()
}

fn at_least(n: usize) -> String {
    format!("SubClassOf(:A DataMinCardinality({n} :dp))")
}

/// The ranges of `NumericsTest.testDecimalMinusInt*`: the xsd:int values from
/// 1.2 to 7.2 that are not integers from 2.2 to 5.2, which are 2, 6 and 7.
const DECIMAL_MINUS_INT: [&str; 3] = [
    r#"DatatypeRestriction(xsd:decimal xsd:minInclusive "1.2"^^xsd:decimal xsd:maxInclusive "7.2"^^xsd:decimal)"#,
    r#"DataComplementOf(DatatypeRestriction(xsd:integer xsd:minInclusive "2.2"^^xsd:decimal xsd:maxInclusive "5.2"^^xsd:decimal))"#,
    "xsd:int",
];

#[test]
fn distinct_values_are_assigned_from_the_remaining_numbers() {
    // Issue #15 (testDecimalMinusIntNEQ_3): no value is left once 2, 6.0 and 7.0
    // are taken.
    let two = r#""2"^^xsd:integer"#;
    let (six, seven) = (r#""6.0"^^xsd:decimal"#, r#""7.0"^^xsd:decimal"#);
    assert!(!consistent(&DECIMAL_MINUS_INT, &distinct_from(&[two, six, seven])));
    assert!(consistent(&DECIMAL_MINUS_INT, &distinct_from(&[six, seven])));
    assert!(consistent(&DECIMAL_MINUS_INT, &distinct_from(&[two, r#""6"^^xsd:integer"#])));
    // A float is not a number of the owl:real value space, so it takes nothing.
    assert!(consistent(&DECIMAL_MINUS_INT, &distinct_from(&[two, six, r#""7.0"^^xsd:float"#])));
    // Three distinct values fit, four do not.
    assert!(consistent(&DECIMAL_MINUS_INT, &at_least(3)));
    assert!(!consistent(&DECIMAL_MINUS_INT, &at_least(4)));
    assert!(consistent(&DECIMAL_MINUS_INT, r#"DataPropertyAssertion(:dp :a "7"^^xsd:int)"#));
    assert!(!consistent(&DECIMAL_MINUS_INT, r#"DataPropertyAssertion(:dp :a "4"^^xsd:int)"#));
}

#[test]
fn excluded_values_are_subtracted() {
    // Issue #16 (testDecimalMinusInt_4): excluding 2, 6.0 and 7.0 leaves nothing.
    let excluding = |members: &str| format!("DataComplementOf(DataOneOf({members}))");
    let all = excluding(r#""2"^^xsd:integer "6.0"^^xsd:decimal "7.0"^^xsd:decimal"#);
    let mut ranges = DECIMAL_MINUS_INT.to_vec();
    ranges.push(&all);
    assert!(!consistent(&ranges, ""));
    // Excluding 6 and 7, however spelt, leaves 2.
    let six_and_seven = excluding(r#""6"^^xsd:integer "12/2"^^owl:rational "7.0"^^xsd:decimal"#);
    let mut ranges = DECIMAL_MINUS_INT.to_vec();
    ranges.push(&six_and_seven);
    assert!(consistent(&ranges, ""));
    assert!(!consistent(&ranges, &at_least(2)));
    assert!(!consistent(&ranges, r#"DataPropertyAssertion(:dp :a "7"^^xsd:integer)"#));
}

#[test]
fn distinct_single_numbers_of_a_dense_range_hold_distinct_values() {
    // Two values from two different single-number ranges can differ.
    let point = |n: &str| {
        format!(
            r#"DatatypeRestriction(xsd:decimal xsd:minInclusive "{n}"^^xsd:decimal xsd:maxInclusive "{n}"^^xsd:decimal)"#
        )
    };
    let axioms = |p: &str, q: &str| {
        format!(
            "ClassAssertion(:A :a)\nDisjointDataProperties(:dp :dq)\n\
             SubClassOf(:A DataSomeValuesFrom(:dp {p}))\n\
             SubClassOf(:A DataSomeValuesFrom(:dq {q}))"
        )
    };
    assert!(consistent_ontology(&axioms(&point("1.5"), &point("2.5"))));
    assert!(!consistent_ontology(&axioms(&point("1.5"), &point("1.5"))));
}

#[test]
fn negated_ranges_leave_finite_integer_windows() {
    // The non-negative integers below 10 are ten values.
    let natural = r#"DatatypeRestriction(xsd:integer xsd:minInclusive "0"^^xsd:integer)"#;
    let not_from_10 =
        r#"DataComplementOf(DatatypeRestriction(xsd:integer xsd:minInclusive "10"^^xsd:integer))"#;
    assert!(consistent(&[natural, not_from_10], &at_least(10)));
    assert!(!consistent(&[natural, not_from_10], &at_least(11)));
    // An exclusive upper bound of -2147483648 admits -2147483649 and below.
    let below = r#"DatatypeRestriction(xsd:integer xsd:maxExclusive "-2147483648"^^xsd:integer)"#;
    let from = r#"DatatypeRestriction(xsd:integer xsd:minInclusive "-2147483650"^^xsd:integer)"#;
    assert!(consistent(&[below, from], &at_least(2)));
    assert!(!consistent(&[below, from], &at_least(3)));
}

#[test]
fn nan_stays_outside_every_float_range_with_facets() {
    // NaN is incomparable, so no range with ordering facets holds it (XSD 1.1
    // Part 2 §3.3.4.1): the floats outside [-INF, +INF] are NaN alone.
    let not_ordered = r#"DataComplementOf(DatatypeRestriction(xsd:float xsd:minInclusive "-INF"^^xsd:float))"#;
    assert!(consistent(&["xsd:float", not_ordered], ""));
    assert!(consistent(&["xsd:float", not_ordered], r#"DataPropertyAssertion(:dp :a "NaN"^^xsd:float)"#));
    assert!(!consistent(&["xsd:float", not_ordered], &at_least(2)));
    let not_nan = r#"DataComplementOf(DataOneOf("NaN"^^xsd:float))"#;
    assert!(!consistent(&["xsd:float", not_ordered, not_nan], ""));
    assert!(!consistent(&["xsd:float", "DataComplementOf(xsd:float)"], ""));
    // A range with facets cut down to one float holds only that float.
    let from_one = r#"DatatypeRestriction(xsd:double xsd:minInclusive "1"^^xsd:double)"#;
    let not_above_one =
        r#"DataComplementOf(DatatypeRestriction(xsd:double xsd:minExclusive "1"^^xsd:double))"#;
    assert!(consistent(&[from_one, not_above_one], ""));
    assert!(!consistent(&[from_one, not_above_one], &at_least(2)));
    assert!(!consistent(&[from_one, not_above_one], r#"DataPropertyAssertion(:dp :a "NaN"^^xsd:double)"#));
}
