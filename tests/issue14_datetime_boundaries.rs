//! Issue #14: a negated dateTime restriction is subtracted from the value space.
//! A dateTime value either has a timezone offset or has none, and each kind is
//! ordered by its instant on the timeline. A value of one kind is smaller or
//! larger than a value of the other only when their instants differ by more than
//! 14 hours, the widest offset (XSD 1.1 Part 2 §D.2.1, OWL 2 Structural
//! Specification §4.7). `DataComplementOf` is the complement within the data
//! domain (OWL 2 Direct Semantics, Table 3).
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

/// Consistency of an ontology with the given axioms.
fn consistent_ontology(axioms: &str) -> bool {
    let source = format!(
        r#"Prefix(:=<urn:issue14:>)
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

fn restriction(facets: &[(&str, &str)]) -> String {
    let facets: String = facets
        .iter()
        .map(|(facet, value)| format!(r#" xsd:{facet} "{value}"^^xsd:dateTime"#))
        .collect();
    format!("DatatypeRestriction(xsd:dateTime{facets})")
}
fn closed(from: &str, to: &str) -> String {
    restriction(&[("minInclusive", from), ("maxInclusive", to)])
}
fn open(from: &str, to: &str) -> String {
    restriction(&[("minExclusive", from), ("maxExclusive", to)])
}
fn complement(range: &str) -> String {
    format!("DataComplementOf({range})")
}
fn value(lexical: &str) -> String {
    format!(r#"DataPropertyAssertion(:dp :a "{lexical}"^^xsd:dateTime)"#)
}
fn at_least(n: usize) -> String {
    format!("SubClassOf(:A DataMinCardinality({n} :dp))")
}

#[test]
fn only_the_bounds_remain() {
    // The ranges of reasoner.DateTimeTest.testFinite2_*: the closed interval
    // between two midnights without an offset, less its interior. A value with
    // an offset is in the closed interval only when it is more than 14 hours
    // inside it, and then it is in the interior too.
    let (a, b) = ("1965-04-15T00:00:00", "1965-05-01T00:00:00");
    let range = [closed(a, b), complement(&open(a, b))];
    let range: Vec<&str> = range.iter().map(String::as_str).collect();
    assert!(consistent(&range, &at_least(2)));
    assert!(!consistent(&range, &at_least(5)));
    assert!(consistent(&range, &value(a)));
    assert!(consistent(&range, &value(b)));
    assert!(!consistent(&range, &value("1965-04-20T00:00:00")));
    assert!(!consistent(&range, &value("1965-04-20T00:00:00Z")));
    assert!(!consistent(&range, &value("1965-04-15T00:00:00Z")));
}

#[test]
fn a_range_less_its_interior_holds_its_two_bounds() {
    let (c, d) = ("2020-06-15T12:30:30", "2020-06-20T12:30:30");
    let range = [closed(c, d), complement(&open(c, d))];
    let range: Vec<&str> = range.iter().map(String::as_str).collect();
    assert!(consistent(&range, &at_least(2)));
    assert!(!consistent(&range, &at_least(3)));
    // Excluding a bound leaves the other; excluding both leaves nothing.
    let not_c = complement(&format!(r#"DataOneOf("{c}"^^xsd:dateTime)"#));
    let not_c_or_d =
        complement(&format!(r#"DataOneOf("{c}"^^xsd:dateTime "{d}"^^xsd:dateTime)"#));
    assert!(consistent(&[range[0], range[1], &not_c], ""));
    assert!(!consistent(&[range[0], range[1], &not_c], &at_least(2)));
    assert!(!consistent(&[range[0], range[1], &not_c_or_d], ""));
    // A closed subtracted interval removes the bounds too.
    assert!(!consistent(&[range[0], &complement(&closed(c, d))], ""));
}

#[test]
fn values_within_14_hours_of_a_bound_of_the_other_kind_remain() {
    // The subtracted interval has offsets and the range has none. A value without
    // an offset is in the subtracted interval only when it is more than 14 hours
    // inside its bounds, so infinitely many values near each bound remain.
    let (c, d) = ("2020-06-15T12:30:30", "2020-06-20T12:30:30");
    let (cz, dz) = ("2020-06-15T12:30:30Z", "2020-06-20T12:30:30Z");
    let range = [closed(c, d), complement(&open(cz, dz))];
    let range: Vec<&str> = range.iter().map(String::as_str).collect();
    assert!(consistent(&range, &at_least(100)));
    assert!(consistent(&range, &value("2020-06-16T02:30:30")));
    assert!(!consistent(&range, &value("2020-06-16T02:30:31")));
    assert!(consistent(&range, &value("2020-06-19T22:30:30")));
    assert!(!consistent(&range, &value("2020-06-19T22:30:29")));
}

#[test]
fn distinct_single_instants_hold_distinct_values() {
    // Two values from two different single-instant ranges can differ: each
    // range holds one value, but not the same one.
    let (c, d) = ("2020-06-15T12:30:30", "2020-06-20T12:30:30");
    let axioms = format!(
        "ClassAssertion(:A :a)\nDisjointDataProperties(:dp :dq)\n\
         SubClassOf(:A DataSomeValuesFrom(:dp {}))\n\
         SubClassOf(:A DataSomeValuesFrom(:dq {}))",
        closed(c, c),
        closed(d, d)
    );
    assert!(consistent_ontology(&axioms));
    let same = format!(
        "ClassAssertion(:A :a)\nDisjointDataProperties(:dp :dq)\n\
         SubClassOf(:A DataSomeValuesFrom(:dp {}))\n\
         SubClassOf(:A DataSomeValuesFrom(:dq {}))",
        closed(c, c),
        closed(c, c)
    );
    assert!(!consistent_ontology(&same));
}
