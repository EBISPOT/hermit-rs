//! Inequalities between data nodes that are fixed to constants. A literal
//! denotes its data value (OWL 2 Direct Semantics §2.2: `(c)^LT` is the value
//! the datatype map assigns to the lexical form), so two literals written
//! differently denote the same value whenever their lexical forms map to equal
//! values. `owl:real`, `owl:rational`, `xsd:decimal` and the integer datatypes
//! share one value space; `xsd:float` and `xsd:double` each have their own,
//! disjoint from it and from each other, as are the string, boolean, binary,
//! anyURI, dateTime and XMLLiteral spaces (OWL 2 Structural Specification §4).
//! A value can therefore not differ from itself, whichever literal names it:
//! `NegativeDataPropertyAssertion(:dp :a v)` (Direct Semantics, Table 6) with
//! `DataPropertyAssertion(:dp :a v')` for an equal `v'`, or two equal values of
//! properties declared disjoint, is inconsistent.
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

fn consistent(axioms: &str) -> bool {
    let source = format!(
        r#"Prefix(:=<urn:constant-inequality:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)
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

/// `a` has value `positive` for `dp`, and does not have value `negative`.
fn negative_assertion(positive: &str, negative: &str) -> bool {
    consistent(&format!(
        "DataPropertyAssertion(:dp :a {positive})\nNegativeDataPropertyAssertion(:dp :a {negative})"
    ))
}

/// `a` has `first` for `dp` and `second` for `dq`, and the two are disjoint.
fn disjoint_properties(first: &str, second: &str) -> bool {
    consistent(&format!(
        "DisjointDataProperties(:dp :dq)\nDataPropertyAssertion(:dp :a {first})\nDataPropertyAssertion(:dq :a {second})"
    ))
}

/// Pairs of literals, written differently, that denote the same value.
const EQUAL_VALUES: [(&str, &str); 12] = [
    (r#""1"^^xsd:int"#, r#""01"^^xsd:int"#),
    (r#""1"^^xsd:int"#, r#""+1"^^xsd:int"#),
    (r#""1"^^xsd:int"#, r#""1"^^xsd:integer"#),
    (r#""1"^^xsd:int"#, r#""1.0"^^xsd:decimal"#),
    (r#""1"^^xsd:byte"#, r#""1"^^xsd:positiveInteger"#),
    (r#""0.5"^^xsd:decimal"#, r#""1/2"^^owl:rational"#),
    (r#""2"^^xsd:nonNegativeInteger"#, r#""4/2"^^owl:rational"#),
    (r#""true"^^xsd:boolean"#, r#""1"^^xsd:boolean"#),
    (r#""1.0"^^xsd:float"#, r#""1"^^xsd:float"#),
    (r#""1.0E0"^^xsd:double"#, r#""1"^^xsd:double"#),
    (r#""abc""#, r#""abc"^^xsd:string"#),
    (r#""0A"^^xsd:hexBinary"#, r#""0a"^^xsd:hexBinary"#),
];

/// Pairs of literals that denote different values, in one value space or in
/// disjoint ones.
const DIFFERENT_VALUES: [(&str, &str); 11] = [
    (r#""1"^^xsd:int"#, r#""2"^^xsd:int"#),
    (r#""1"^^xsd:int"#, r#""1.5"^^xsd:decimal"#),
    (r#""1/3"^^owl:rational"#, r#""0.3333"^^xsd:decimal"#),
    (r#""0.0"^^xsd:float"#, r#""-0.0"^^xsd:float"#),
    // Disjoint value spaces: equal-looking literals are still distinct values.
    (r#""1"^^xsd:int"#, r#""1"^^xsd:float"#),
    (r#""1"^^xsd:int"#, r#""1"^^xsd:double"#),
    (r#""1"^^xsd:float"#, r#""1"^^xsd:double"#),
    (r#""1"^^xsd:int"#, r#""1"^^xsd:string"#),
    (r#""true"^^xsd:boolean"#, r#""1"^^xsd:integer"#),
    (r#""abc""#, r#""abc"@en"#),
    (r#""http://x/"^^xsd:anyURI"#, r#""http://x/"^^xsd:string"#),
];

#[test]
fn negative_assertion_of_an_equal_value_written_differently_is_inconsistent() {
    for (positive, negative) in EQUAL_VALUES {
        assert!(!negative_assertion(positive, negative), "{positive} vs ¬{negative}");
        assert!(!negative_assertion(negative, positive), "{negative} vs ¬{positive}");
    }
}

#[test]
fn disjoint_properties_with_equal_values_written_differently_are_inconsistent() {
    for (first, second) in EQUAL_VALUES {
        assert!(!disjoint_properties(first, second), "{first} vs {second}");
    }
}

#[test]
fn different_values_stay_consistent() {
    for (first, second) in DIFFERENT_VALUES {
        assert!(negative_assertion(first, second), "{first} vs ¬{second}");
        assert!(negative_assertion(second, first), "{second} vs ¬{first}");
        assert!(disjoint_properties(first, second), "{first} vs {second}");
    }
}

/// An identical literal on both sides is the same constant node, which already
/// clashed; the fix must keep that.
#[test]
fn identical_literals_are_inconsistent() {
    assert!(!negative_assertion(r#""1"^^xsd:int"#, r#""1"^^xsd:int"#));
    assert!(!disjoint_properties(r#""1"^^xsd:int"#, r#""1"^^xsd:int"#));
}

/// A fresh data node pinned by a range to one value must differ from a
/// constant with that value, and from another node pinned to it.
#[test]
fn nodes_pinned_to_equal_values_clash() {
    assert!(!consistent(
        r#"DataPropertyAssertion(:dp :a "01"^^xsd:int)
ClassAssertion(DataAllValuesFrom(:dq DataOneOf("1.0"^^xsd:decimal)) :a)
ClassAssertion(DataSomeValuesFrom(:dq rdfs:Literal) :a)
DisjointDataProperties(:dp :dq)"#
    ));
    assert!(!consistent(
        r#"ClassAssertion(DataSomeValuesFrom(:dp DataOneOf("1"^^xsd:int)) :a)
ClassAssertion(DataSomeValuesFrom(:dq DataOneOf("1/1"^^owl:rational)) :a)
DisjointDataProperties(:dp :dq)"#
    ));
    assert!(!consistent(
        r#"DataPropertyAssertion(:dp :a "01"^^xsd:int)
ClassAssertion(DataSomeValuesFrom(:dq DataOneOf("1"^^xsd:integer "1.0"^^xsd:decimal)) :a)
DisjointDataProperties(:dp :dq)"#
    ));
    assert!(!consistent(
        r#"DataPropertyAssertion(:dp :a "1.0"^^xsd:decimal)
ClassAssertion(DataSomeValuesFrom(:dq DatatypeRestriction(xsd:integer xsd:minInclusive "1"^^xsd:int xsd:maxInclusive "1"^^xsd:int)) :a)
DisjointDataProperties(:dp :dq)"#
    ));
    assert!(!consistent(
        r#"ClassAssertion(DataMinCardinality(2 :dp DataOneOf("1"^^xsd:int "01"^^xsd:byte "1/1"^^owl:rational)) :a)"#
    ));
    assert!(consistent(
        r#"DataPropertyAssertion(:dp :a "01"^^xsd:int)
ClassAssertion(DataSomeValuesFrom(:dq DataOneOf("1"^^xsd:float)) :a)
DisjointDataProperties(:dp :dq)"#
    ));
    assert!(consistent(
        r#"DataPropertyAssertion(:dp :a "1"^^xsd:int)
ClassAssertion(DataSomeValuesFrom(:dq DatatypeRestriction(xsd:integer xsd:minInclusive "1"^^xsd:int xsd:maxInclusive "2"^^xsd:int)) :a)
DisjointDataProperties(:dp :dq)"#
    ));
}

/// A functional data property merges the two values of `a`: that is
/// consistent exactly when the literals denote one value.
#[test]
fn functional_property_values_merge_by_value() {
    let functional = |first: &str, second: &str| {
        consistent(&format!(
            "FunctionalDataProperty(:dp)\nDataPropertyAssertion(:dp :a {first})\nDataPropertyAssertion(:dp :a {second})"
        ))
    };
    for (first, second) in EQUAL_VALUES {
        assert!(functional(first, second), "{first} = {second}");
    }
    for (first, second) in DIFFERENT_VALUES {
        assert!(!functional(first, second), "{first} = {second}");
    }
}
