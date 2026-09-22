use super::*;
use hermit_rs::structural::{Fact, OWLAxioms, OWLNormalization};

pub(super) fn canonical(text: &str) -> String {
    fn expression(tokens: &[String], at: &mut usize) -> String {
        let name = tokens[*at].clone();
        *at += 1;
        if tokens.get(*at).is_none_or(|s| s != "(") {
            return name;
        }
        *at += 1;
        let mut args = Vec::new();
        while tokens[*at] != ")" {
            args.push(expression(tokens, at));
        }
        *at += 1;
        if matches!(
            name.as_str(),
            "ObjectUnionOf"
                | "ObjectIntersectionOf"
                | "ObjectOneOf"
                | "DataUnionOf"
                | "DataIntersectionOf"
                | "DataOneOf"
                | "EquivalentClasses"
                | "EquivalentObjectProperties"
                | "EquivalentDataProperties"
                | "SameIndividual"
                | "DifferentIndividuals"
                | "DisjointClasses"
        ) {
            args.sort();
        }
        format!("{name}({})", args.join(" "))
    }
    static TOKENIZER: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    let re = TOKENIZER.get_or_init(|| {
        regex::Regex::new(r#""(?:\\.|[^"\\])*"(?:\^\^<[^>]*>|@[\w-]+)?|<[^>]*>|[^\s()]+|[()]"#)
            .unwrap()
    });
    let tokens: Vec<String> = re.find_iter(text).map(|m| m.as_str().to_string()).collect();
    let mut at = 0;
    let mut out = Vec::new();
    while at < tokens.len() {
        out.push(expression(&tokens, &mut at));
    }
    out.join(" ")
}
fn normalized(o: &O) -> HashSet<String> {
    let b = Build::new_arc();
    let mut n = OWLNormalization::new(OWLAxioms::new(), 0);
    n.process_ontology(o).unwrap();
    let a = n.into_axioms();
    let mut components = Vec::<Component<A>>::new();
    for inclusion in a.concept_inclusions {
        let sup = if inclusion.len() == 1 {
            inclusion[0].clone()
        } else {
            CE::ObjectUnionOf(inclusion)
        };
        components.push(
            SubClassOf {
                sub: CE::Class(b.class("http://www.w3.org/2002/07/owl#Thing")),
                sup,
            }
            .into(),
        );
    }
    for [sub, sup] in a.simple_object_property_inclusions {
        components.push(
            SubObjectPropertyOf {
                sub: SubObjectPropertyExpression::ObjectPropertyExpression(sub),
                sup,
            }
            .into(),
        );
    }
    for [sub, sup] in a.data_property_inclusions {
        components.push(SubDataPropertyOf { sub, sup }.into());
    }
    for key in a.has_keys {
        components.push(
            HasKey {
                ce: key.class_expression,
                vpe: key.property_expressions,
            }
            .into(),
        );
    }
    for fact in a.facts {
        components.push(match fact {
            Fact::SameIndividual(v) => SameIndividual(v).into(),
            Fact::DifferentIndividuals(v) => DifferentIndividuals(v).into(),
            Fact::ClassAssertion {
                class_expression,
                individual,
            } => ClassAssertion {
                ce: class_expression,
                i: individual,
            }
            .into(),
            Fact::ObjectPropertyAssertion { ope, from, to } => {
                ObjectPropertyAssertion { ope, from, to }.into()
            }
            Fact::NegativeObjectPropertyAssertion { ope, from, to } => {
                NegativeObjectPropertyAssertion { ope, from, to }.into()
            }
            Fact::DataPropertyAssertion { dp, from, to } => {
                DataPropertyAssertion { dp, from, to }.into()
            }
            Fact::NegativeDataPropertyAssertion { dp, from, to } => {
                NegativeDataPropertyAssertion { dp, from, to }.into()
            }
        });
    }
    components
        .iter()
        .map(|a| canonical(&a.as_functional().to_string()))
        .collect()
}
pub(super) fn run(row: &Value) {
    let o = ontology(&row["ontology"]);
    if row["op"] == "normalize" {
        let expected: HashSet<_> = row["expected"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| canonical(&axiom(v.as_str().unwrap()).as_functional().to_string()))
            .collect();
        assert_eq!(normalized(&o), expected);
        return;
    }
    let mut reasoner = r::IncrementalReasoner::new(o);
    let dl = reasoner.dl_ontology();
    let mut prefixes = hermit_rs::prefixes::Prefixes::new();
    prefixes.declare_semantic_web_prefixes();
    prefixes.declare_internal_prefixes(std::iter::empty::<&str>(), std::iter::empty::<&str>());
    prefixes
        .declare_default_prefix("file:/c/test.owl#")
        .unwrap();
    let mut actual = std::collections::BTreeSet::new();
    for clause in dl.get_dl_clauses() {
        let mut head: Vec<_> = clause
            .get_head_atoms()
            .iter()
            .map(|a| a.to_string_prefixes(&prefixes))
            .collect();
        head.sort();
        let mut body: Vec<_> = clause
            .get_body_atoms()
            .iter()
            .map(|a| a.to_string_prefixes(&prefixes))
            .collect();
        body.sort();
        actual.insert(format!("{} :- {}", head.join(" v "), body.join(", ")));
    }
    for a in dl.get_positive_facts() {
        actual.insert(a.to_string_prefixes(&prefixes));
    }
    for a in dl.get_negative_facts() {
        actual.insert(format!("not {}", a.to_string_prefixes(&prefixes)));
    }
    let expected = row["expected"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s.as_str().unwrap().to_string())
        .collect();
    assert_eq!(actual, expected);
}
