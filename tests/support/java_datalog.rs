use super::*;
use hermit_rs::datalog::{ConjunctiveQuery, DatalogEngine, QueryAtom, QueryTerm};
const NS: &str = "file:/c/test.owl#";
fn v(s: &str) -> QueryTerm {
    QueryTerm::Variable(s.into())
}
fn i(s: &str) -> QueryTerm {
    QueryTerm::Individual(format!("{NS}{s}"))
}
fn role(s: &str, a: QueryTerm, b: QueryTerm) -> QueryAtom {
    QueryAtom::Role(property(&format!("<{NS}{s}>")), a, b)
}
fn answers(
    e: &DatalogEngine,
    atoms: Vec<QueryAtom>,
    terms: Vec<QueryTerm>,
    expected: Vec<Vec<String>>,
) {
    let mut actual: Vec<Vec<String>> = Vec::new();
    ConjunctiveQuery::new(atoms, terms)
        .evaluate(e, &mut actual)
        .unwrap();
    actual.sort();
    let mut expected = expected;
    expected.sort();
    assert_eq!(actual, expected);
}
pub(super) fn run(case: &Value) {
    let e = DatalogEngine::new(&ontology(&case["operations"][0]["ontology"])).unwrap();
    let method = case["java"].as_str().unwrap().rsplit('.').next().unwrap();
    let individual = |s: &str| hermit_rs::model::Individual::create(format!("{NS}{s}"));
    let equivalent = |names: &[&str]| {
        let got: HashSet<_> = e
            .get_equivalence_class(&individual("a"))
            .unwrap()
            .into_iter()
            .collect();
        assert_eq!(got, names.iter().map(|s| individual(s)).collect());
    };
    match method {
        "testBasic" => {
            for (c, expected) in [
                ("A", vec!["a", "b", "c", "d", "n"]),
                ("B", vec!["c", "d", "k", "l", "m", "n"]),
                ("C", vec!["c", "d", "n"]),
            ] {
                answers(
                    &e,
                    vec![QueryAtom::Concept(
                        expression(&format!("<{NS}{c}>")),
                        v("X"),
                    )],
                    vec![v("X")],
                    expected.iter().map(|s| vec![format!("{NS}{s}")]).collect(),
                );
            }
        }
        "testEquality" => {
            equivalent(&["a", "c", "e", "g"]);
            let representative = e
                .get_representative(&individual("a"))
                .unwrap()
                .unwrap()
                .iri()
                .to_string();
            answers(
                &e,
                vec![role("R", v("X"), v("Y"))],
                vec![v("X"), v("Y")],
                ["b", "d", "f"]
                    .map(|s| vec![format!("{NS}{s}"), representative.clone()])
                    .to_vec(),
            );
        }
        "testQueryWithIndividualsAndEquality" => {
            equivalent(&["a", "b"]);
            answers(
                &e,
                vec![role("R", v("X"), i("a")), role("S", v("X"), i("b"))],
                vec![v("X")],
                vec![vec![format!("{NS}c")]],
            );
        }
        "testQueryWithIndividuals" => {
            answers(&e, vec![role("R", v("X"), i("a"))], vec![v("X")], vec![])
        }
        _ => panic!("unhandled datalog case {method}"),
    }
}
