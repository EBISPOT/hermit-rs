//! `24:00:00` in an `xsd:dateTime` is a lexical alternative for `00:00:00` of
//! the next day. XSD 1.1 Part 2 §3.3.7.2 and the lexical mapping of §E.3.5 map
//! hour 24 (allowed only with zero minutes and seconds) to hour 0 of the next
//! day, so both spellings denote one value, with the same timezone offset if
//! any; OWL 2 Structural Specification §4.7 takes xsd:dateTime and
//! xsd:dateTimeStamp from XSD 1.1. HermiT keeps the two spellings apart as two
//! values (`DateTime.m_lastDayInstant`), which made a functional data property
//! asserted with both spellings inconsistent and let a single instant hold two
//! values; this port deliberately follows XSD instead.
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

fn consistent(axioms: &str) -> bool {
    check(axioms).unwrap()
}

fn check(axioms: &str) -> Result<bool, String> {
    let source = format!(
        r#"Prefix(:=<urn:datetime-24h:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
Declaration(Class(:C))
Declaration(NamedIndividual(:a))
Declaration(DataProperty(:dp))
{axioms}
)"#
    );
    let ontology: SetOntology<A> =
        horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
            .unwrap()
            .0;
    reasoner::is_ontology_consistent(&ontology)
}

fn dt(lexical: &str) -> String {
    format!(r#""{lexical}"^^xsd:dateTime"#)
}

/// `a` has both values for the functional `dp`.
fn functional(first: &str, second: &str) -> bool {
    consistent(&format!(
        "FunctionalDataProperty(:dp)\nDataPropertyAssertion(:dp :a {first})\nDataPropertyAssertion(:dp :a {second})"
    ))
}

/// `a` has `positive` for `dp`, and does not have `negative`.
fn negative(positive: &str, negative: &str) -> bool {
    consistent(&format!(
        "DataPropertyAssertion(:dp :a {positive})\nNegativeDataPropertyAssertion(:dp :a {negative})"
    ))
}

/// Pairs of literals that name one value.
const SAME: [(&str, &str); 7] = [
    ("2020-01-01T24:00:00Z", "2020-01-02T00:00:00Z"),
    ("2020-01-01T24:00:00", "2020-01-02T00:00:00"),
    ("2020-01-01T24:00:00.0Z", "2020-01-02T00:00:00Z"),
    ("2020-01-01T24:00:00.000+05:30", "2020-01-02T00:00:00+05:30"),
    ("2020-12-31T24:00:00-14:00", "2021-01-01T00:00:00-14:00"),
    ("2020-02-28T24:00:00Z", "2020-02-29T00:00:00Z"),
    ("-0001-12-31T24:00:00Z", "0000-01-01T00:00:00Z"),
];

/// Pairs of literals that name different values.
const DIFFERENT: [(&str, &str); 4] = [
    // A different day.
    ("2020-01-01T24:00:00Z", "2020-01-01T00:00:00Z"),
    // With and without a timezone offset.
    ("2020-01-01T24:00:00Z", "2020-01-02T00:00:00"),
    // Another offset, at another instant.
    ("2020-01-01T24:00:00+01:00", "2020-01-02T00:00:00Z"),
    // One millisecond later.
    ("2020-01-01T24:00:00Z", "2020-01-02T00:00:00.001Z"),
];

#[test]
fn end_of_day_spelling_is_the_next_midnight() {
    for (first, second) in SAME {
        let (first, second) = (dt(first), dt(second));
        assert!(functional(&first, &second), "{first} = {second}");
        assert!(functional(&second, &first), "{second} = {first}");
        assert!(!negative(&first, &second), "{first} = {second}");
        assert!(!negative(&second, &first), "{second} = {first}");
    }
    for (first, second) in DIFFERENT {
        let (first, second) = (dt(first), dt(second));
        assert!(!functional(&first, &second), "{first} != {second}");
        assert!(negative(&first, &second), "{first} != {second}");
    }
    // xsd:dateTimeStamp has the same values, with a required offset.
    let stamp = r#""2020-01-01T24:00:00Z"^^xsd:dateTimeStamp"#;
    assert!(functional(stamp, &dt("2020-01-02T00:00:00Z")));
    assert!(!negative(stamp, &dt("2020-01-02T00:00:00Z")));
}

#[test]
fn end_of_day_spelling_in_ranges() {
    // Enumerations and interval bounds see one value.
    let member = |range: &str, value: &str| {
        !consistent(&format!(
            "DataPropertyAssertion(:dp :a {})\nClassAssertion(DataAllValuesFrom(:dp DataComplementOf({range})) :a)",
            dt(value)
        ))
    };
    let one_of = format!("DataOneOf({})", dt("2020-01-01T24:00:00Z"));
    assert!(member(&one_of, "2020-01-02T00:00:00Z"));
    assert!(!member(&one_of, "2020-01-01T00:00:00Z"));
    let from = |facet: &str| {
        format!("DatatypeRestriction(xsd:dateTime xsd:{facet} {})", dt("2020-01-01T24:00:00Z"))
    };
    assert!(member(&from("minInclusive"), "2020-01-02T00:00:00Z"));
    assert!(!member(&from("minExclusive"), "2020-01-02T00:00:00Z"));
    assert!(member(&from("maxInclusive"), "2020-01-02T00:00:00Z"));
    assert!(!member(&from("maxExclusive"), "2020-01-02T00:00:00Z"));
    // The two spellings in one enumeration are one value.
    let both = format!(
        "DataOneOf({} {})",
        dt("2020-01-01T24:00:00Z"),
        dt("2020-01-02T00:00:00Z")
    );
    assert!(!consistent(&format!(
        "ClassAssertion(DataMinCardinality(2 :dp {both}) :a)"
    )));
    assert!(consistent(&format!(
        "ClassAssertion(DataMinCardinality(1 :dp {both}) :a)"
    )));
}

#[test]
fn single_instant_holds_one_value_per_offset() {
    // Without a timezone offset, a single instant is one value, even at
    // midnight, where HermiT counts `24:00:00` of the previous day again.
    let instant = |lexical: &str| {
        format!(
            "DatatypeRestriction(xsd:dateTime xsd:minInclusive {v} xsd:maxInclusive {v})",
            v = dt(lexical)
        )
    };
    for lexical in ["1965-04-15T00:00:00", "1965-04-14T24:00:00", "1965-04-15T12:30:00"] {
        let range = instant(lexical);
        assert!(consistent(&format!("ClassAssertion(DataMinCardinality(1 :dp {range}) :a)")));
        assert!(
            !consistent(&format!("ClassAssertion(DataMinCardinality(2 :dp {range}) :a)")),
            "{lexical}"
        );
    }
    // A closed interval less its open interior holds just its two bounds.
    let bounds = format!(
        "DataIntersectionOf(DatatypeRestriction(xsd:dateTime xsd:minInclusive {a} xsd:maxInclusive {b}) DataComplementOf(DatatypeRestriction(xsd:dateTime xsd:minExclusive {a} xsd:maxExclusive {b})))",
        a = dt("1965-04-15T00:00:00"),
        b = dt("1965-05-01T00:00:00")
    );
    assert!(consistent(&format!("ClassAssertion(DataMinCardinality(2 :dp {bounds}) :a)")));
    assert!(!consistent(&format!("ClassAssertion(DataMinCardinality(3 :dp {bounds}) :a)")));
}

#[test]
fn end_of_day_lexical_edge_cases() {
    // Hour 24 is valid only with zero minutes, seconds and fraction; any other
    // form is malformed, and the ontology is rejected, as in HermiT.
    for valid in ["2020-01-01T24:00:00", "2020-01-01T24:00:00.0", "2020-01-01T24:00:00.000Z", "2020-01-01T24:00:00+14:00"] {
        assert!(consistent(&format!("DataPropertyAssertion(:dp :a {})", dt(valid))), "{valid}");
    }
    for invalid in ["2020-01-01T24:00:01", "2020-01-01T24:01:00Z", "2020-01-01T24:00:00.001Z", "2020-01-01T25:00:00Z"] {
        let outcome = check(&format!("DataPropertyAssertion(:dp :a {})", dt(invalid)));
        assert!(outcome.is_err_and(|e| e.contains("MalformedLiteral")), "{invalid}");
    }
    // xsd:dateTimeStamp requires the offset.
    let outcome = check(r#"DataPropertyAssertion(:dp :a "2020-01-01T24:00:00"^^xsd:dateTimeStamp)"#);
    assert!(outcome.is_err_and(|e| e.contains("MalformedLiteral")));
}
