//! Replay the original Java suite's checked query traces against Rust.
//! Each case runs in a separate process: a timeout kills and reaps that process.
#[path = "support/java_datalog.rs"]
mod java_datalog;
#[path = "support/java_outcome.rs"]
mod java_outcome;
#[path = "support/java_structural.rs"]
mod java_structural;
#[path = "support/memory_budget.rs"]
mod memory_budget;
use hermit_rs::{
    configuration::*,
    node_set::{group_by_equivalence, NodeSet},
    reasoner as r,
    structural::A,
};
use horned_owl::io::ofn::writer::AsFunctional;
use horned_owl::{model::*, ontology::set::SetOntology};
use serde_json::{json, Value};
use std::{
    collections::{HashMap, HashSet},
    io::Cursor,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};
type O = SetOntology<A>;
type CE = ClassExpression<A>;
type OPE = ObjectPropertyExpression<A>;
const ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/java");
const PREFIXES: &str = "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>) Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>) Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)";
fn parse(src: &str) -> O {
    let src = java_syntax(src);
    let src = format!("{PREFIXES}\n{src}");
    horned_owl::io::ofn::reader::read(&mut Cursor::new(src.as_bytes()), Default::default())
        .expect("functional syntax fixture")
        .0
}
fn ontology(name: &Value) -> O {
    parse(
        &std::fs::read_to_string(
            Path::new(ROOT)
                .join("ontologies")
                .join(name.as_str().unwrap()),
        )
        .unwrap(),
    )
}
fn axiom(s: &str) -> Component<A> {
    let o = parse(&format!("{PREFIXES} Ontology({s})"));
    o.into_iter()
        .find(|a| !matches!(a.component, Component::OntologyID(_)))
        .expect("query axiom")
        .component
        .clone()
}
fn expression(s: &str) -> CE {
    match axiom(&format!("SubClassOf({s} owl:Thing)")) {
        Component::SubClassOf(a) => a.sub,
        _ => unreachable!(),
    }
}
fn property(s: &str) -> OPE {
    match expression(&format!("ObjectSomeValuesFrom({s} owl:Thing)")) {
        CE::ObjectSomeValuesFrom { ope, .. } => ope,
        _ => unreachable!(),
    }
}
fn iri(s: &str) -> String {
    if let Some(v) = s.strip_prefix('<').and_then(|v| v.strip_suffix('>')) {
        return v.into();
    }
    for (prefix, base) in [
        ("owl:", "http://www.w3.org/2002/07/owl#"),
        ("xsd:", "http://www.w3.org/2001/XMLSchema#"),
        ("rdf:", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
        ("rdfs:", "http://www.w3.org/2000/01/rdf-schema#"),
    ] {
        if let Some(v) = s.strip_prefix(prefix) {
            return format!("{base}{v}");
        }
    }
    panic!("not an IRI: {s}")
}
trait Render {
    fn render(&self) -> String;
}
macro_rules! render_iri {($($t:ident),*)=>{$(impl Render for $t<A>{fn render(&self)->String {format!("<{}>",self.0)}})*};}
render_iri!(Class, NamedIndividual, ObjectProperty, DataProperty);
impl Render for Literal<A> {
    fn render(&self) -> String {
        self.as_functional()
            .to_string()
            .trim_end_matches("^^<http://www.w3.org/2001/XMLSchema#string>")
            .to_string()
    }
}
impl Render for OPE {
    fn render(&self) -> String {
        match self {
            Self::ObjectProperty(p) => p.render(),
            Self::InverseObjectProperty(p) => format!("ObjectInverseOf({})", p.render()),
        }
    }
}
fn set<E: Render>(xs: impl IntoIterator<Item = E>) -> Value {
    Value::Array(xs.into_iter().map(|x| Value::String(x.render())).collect())
}
fn nodes<E: Render + Eq + std::hash::Hash + Clone>(xs: NodeSet<E>) -> Value {
    Value::Array(xs.into_iter().map(|n| set(n.into_entities())).collect())
}
fn normalize(v: &mut Value) {
    match v {
        Value::Array(xs) => {
            for x in xs.iter_mut() {
                normalize(x)
            }
            xs.sort_by_key(|x| x.to_string());
        }
        Value::Object(xs) => {
            for x in xs.values_mut() {
                normalize(x)
            }
        }
        _ => {}
    }
}
fn config(row: &Value) -> Configuration {
    Configuration {
        blocking_strategy_type: match row["blocking"].as_str().unwrap() {
            "OPTIMAL" => BlockingStrategyType::Optimal,
            "ANYWHERE" => BlockingStrategyType::Anywhere,
            "ANCESTOR" => BlockingStrategyType::Ancestor,
            "SIMPLE_CORE" => BlockingStrategyType::SimpleCore,
            "COMPLEX_CORE" => BlockingStrategyType::ComplexCore,
            x => panic!("blocking {x}"),
        },
        direct_blocking_type: match row["direct_blocking"].as_str().unwrap() {
            "OPTIMAL" => DirectBlockingType::Optimal,
            "SINGLE" => DirectBlockingType::Single,
            "PAIR_WISE" => DirectBlockingType::PairWise,
            x => panic!("direct blocking {x}"),
        },
        blocking_signature_cache_type: match row["cache"].as_str().unwrap() {
            "CACHED" => BlockingSignatureCacheType::Cached,
            "NOT_CACHED" => BlockingSignatureCacheType::NotCached,
            x => panic!("cache {x}"),
        },
        existential_strategy_type: match row["existential"].as_str().unwrap() {
            "CREATION_ORDER" => ExistentialStrategyType::CreationOrder,
            "INDIVIDUAL_REUSE" => ExistentialStrategyType::IndividualReuse,
            "EL" => ExistentialStrategyType::El,
            x => panic!("existential {x}"),
        },
        individual_node_set_policy: if row["individual_policy"] == "BY_SAME_AS" {
            IndividualNodeSetPolicy::BySameAs
        } else {
            IndividualNodeSetPolicy::ByName
        },
        throw_inconsistent_ontology_exception: row["throw_inconsistent"].as_bool().unwrap(),
        buffer_changes: row["buffer_changes"].as_bool().unwrap_or(true),
        ignore_unsupported_datatypes: row["ignore_unsupported"].as_bool().unwrap_or(false),
        ..Configuration::default()
    }
}
fn apply_delta(reasoner: &mut r::IncrementalReasoner, new: &O) {
    let old: HashSet<_> = reasoner
        .ontology()
        .into_iter()
        .map(|a| a.component.clone())
        .collect();
    let new: HashSet<_> = new.into_iter().map(|a| a.component.clone()).collect();
    for a in old.difference(&new) {
        reasoner.remove_axiom(a.clone());
    }
    for a in new.difference(&old) {
        reasoner.add_axiom(a.clone());
    }
}
fn query(reasoner: &mut r::IncrementalReasoner, row: &Value) -> Result<Value, String> {
    let b = Build::new_arc();
    let args = row["args"].as_array().unwrap();
    let s = |i: usize| args[i].as_str().unwrap();
    let boolean = |i: usize| args[i].as_bool().unwrap();
    let individual = |i: usize| b.named_individual(iri(s(i)));
    let dp = |i: usize| b.data_property(iri(s(i)));
    let o = reasoner.ontology();
    let c = reasoner.configuration();
    Ok(match row["op"].as_str().unwrap() {
        "classifyClasses" => {
            reasoner.classify()?;
            Value::Null
        }
        "precomputeInferences" => {
            use r::InferenceType::*;
            let mut types = Vec::new();
            for name in args[0].as_array().unwrap() {
                types.push(match name.as_str().unwrap() {
                    "class hierarchy" => ClassHierarchy,
                    "object property hierarchy" => ObjectPropertyHierarchy,
                    "data property hierarchy" => DataPropertyHierarchy,
                    "class assertions" => ClassAssertions,
                    "object property assertions" => ObjectPropertyAssertions,
                    "same individual" => SameIndividual,
                    // These are deliberately ignored by Java's precompute API.
                    "disjoint classes" | "different individuals" | "data property assertions" => {
                        continue
                    }
                    other => panic!("unhandled Java inference type: {other}"),
                });
            }
            reasoner.precompute(&types)?;
            Value::Null
        }
        "isConsistent" => json!(reasoner.is_consistent()?),
        "isSatisfiable" => json!(reasoner.is_concept_satisfiable(expression(s(0)))?),
        "isEntailed" => {
            let axioms = if let Some(a) = args[0].as_array() {
                a.iter()
                    .map(|s| axiom(s.as_str().unwrap()))
                    .collect::<Vec<_>>()
            } else {
                vec![axiom(s(0))]
            };
            if !reasoner.is_consistent()?
                && !reasoner
                    .configuration()
                    .throw_inconsistent_ontology_exception
            {
                json!(true)
            } else {
                json!(r::is_entailed_axioms(reasoner.ontology(), &axioms)?)
            }
        }
        "hasType" => {
            if !boolean(2) {
                json!(reasoner.is_instance_of(individual(0), expression(s(1)))?)
            } else {
                json!(
                    r::instances_of_expression_with_configuration(o, &expression(s(1)), true, c)?
                        .contains(&individual(0))
                )
            }
        }
        "getInstances" => {
            let xs =
                r::instances_of_expression_with_configuration(o, &expression(s(0)), boolean(1), c)?;
            if c.individual_node_set_policy == IndividualNodeSetPolicy::BySameAs {
                nodes(group_by_equivalence(xs, |i| {
                    r::get_same_individuals(o, i).unwrap()
                }))
            } else {
                Value::Array(xs.into_iter().map(|i| json!([i.render()])).collect())
            }
        }
        "getSuperClasses" | "getSubClasses" | "getEquivalentClasses" | "getDisjointClasses" => {
            let ce = expression(s(0));
            let h = r::classify_with_configuration(o, c)?;
            let op = row["op"].as_str().unwrap();
            let xs = match (&ce, op) {
                (CE::Class(cl), "getSuperClasses") => h.super_elements(cl, boolean(1)),
                (CE::Class(cl), "getSubClasses") => h.sub_elements(cl, boolean(1)),
                (CE::Class(cl), "getEquivalentClasses") => h.equivalent_elements_of(cl),
                (_, "getSuperClasses") => r::super_classes_of_expression(o, &ce, boolean(1))?,
                (_, "getSubClasses") => r::sub_classes_of_expression(o, &ce, boolean(1))?,
                (_, "getEquivalentClasses") => r::equivalent_classes_of_expression(o, &ce)?,
                _ => r::disjoint_classes_of_expression(o, &ce)?,
            };
            if op == "getEquivalentClasses" {
                set(xs)
            } else {
                nodes(group_by_equivalence(xs, |e| h.equivalent_elements_of(e)))
            }
        }
        "getSubObjectProperties"
        | "getSuperObjectProperties"
        | "getEquivalentObjectProperties"
        | "getInverseObjectProperties"
        | "getDisjointObjectProperties" => {
            let p = property(s(0));
            let h = r::classify_object_property_expressions_with_configuration(o, c)?;
            let op = row["op"].as_str().unwrap();
            let xs = match op {
                "getSubObjectProperties" => h.sub_elements(&p, boolean(1)),
                "getSuperObjectProperties" => h.super_elements(&p, boolean(1)),
                "getEquivalentObjectProperties" => h.equivalent_elements_of(&p),
                "getInverseObjectProperties" => {
                    h.equivalent_elements_of(&hermit_rs::structural::inverse_property(&p))
                }
                _ => r::get_disjoint_object_properties(o, &p)?,
            };
            if op == "getEquivalentObjectProperties" || op == "getInverseObjectProperties" {
                set(xs)
            } else {
                nodes(group_by_equivalence(xs, |e| h.equivalent_elements_of(e)))
            }
        }
        "getSuperDataProperties" | "getSubDataProperties" | "getEquivalentDataProperties" => {
            let p = dp(0);
            let h = r::classify_data_properties_with_configuration(o, c)?;
            let op = row["op"].as_str().unwrap();
            let xs = match op {
                "getSuperDataProperties" => h.super_elements(&p, boolean(1)),
                "getSubDataProperties" => h.sub_elements(&p, boolean(1)),
                _ => h.equivalent_elements_of(&p),
            };
            if op == "getEquivalentDataProperties" {
                set(xs)
            } else {
                nodes(group_by_equivalence(xs, |e| h.equivalent_elements_of(e)))
            }
        }
        "getDataPropertyValues" => set(r::get_data_property_values(o, &individual(0), dp(1))?),
        "getTypes" => nodes(r::type_nodes_with_configuration(
            o,
            &individual(0),
            boolean(1),
            c,
        )?),
        "getSameIndividuals" => set(r::get_same_individuals(o, &individual(0))?),
        "getObjectPropertyInstances" => {
            let mut result = serde_json::Map::new();
            for (subject, object) in r::object_property_instances(o, property(s(0)))? {
                result
                    .entry(subject.render())
                    .or_insert_with(|| json!([]))
                    .as_array_mut()
                    .unwrap()
                    .push(json!(object.render()));
            }
            Value::Object(result)
        }
        "hasObjectPropertyRelationship" => json!(r::has_object_property_relationship(
            o,
            &individual(0),
            property(s(1)),
            &individual(2)
        )?),
        "getObjectPropertyValues" => {
            let xs = r::get_object_property_values(o, &individual(0), property(s(1)))?;
            if c.individual_node_set_policy == IndividualNodeSetPolicy::BySameAs {
                nodes(group_by_equivalence(xs, |i| {
                    r::get_same_individuals(o, i).unwrap()
                }))
            } else {
                Value::Array(xs.into_iter().map(|i| json!([i.render()])).collect())
            }
        }
        "getObjectPropertyDomains" | "getObjectPropertyRanges" => {
            let xs = if row["op"] == "getObjectPropertyDomains" {
                r::get_object_property_domains(o, &property(s(0)), boolean(1))?
            } else {
                r::get_object_property_ranges(o, &property(s(0)), boolean(1))?
            };
            let h = r::classify_with_configuration(o, c)?;
            nodes(group_by_equivalence(xs, |e| h.equivalent_elements_of(e)))
        }
        "printHierarchies" => json!(r::print_hierarchies_with_configuration(
            o,
            boolean(0),
            boolean(1),
            boolean(2),
            c
        )?),
        other => return Err(format!("unimplemented Java test operation: {other}")),
    })
}
// Replaces a recorded Java expectation that contradicts the OWL 2 or XSD
// specifications with its documented correction (`java/corrections.json`). The
// trace keeps the Java value, and the correction applies only while it still
// matches, so regenerated traces cannot silently change what is corrected.
fn correct(name: &str, rows: &mut [Value]) {
    let corrections: HashMap<String, Value> =
        serde_json::from_str(include_str!("java/corrections.json")).unwrap();
    let Some(correction) = corrections.get(name) else {
        return;
    };
    let row = &mut rows[correction["operation"].as_u64().unwrap() as usize];
    assert_eq!(
        (&row["op"], &row["expected"]),
        (&correction["op"], &correction["java"]),
        "{name}: stale correction of the recorded Java expectation"
    );
    row["expected"] = correction["corrected"].clone();
}
fn run_case(path: &Path) {
    let case: Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    if case["java"]
        .as_str()
        .unwrap()
        .starts_with("reasoner.DatalogEngineTest.")
    {
        java_datalog::run(&case);
        return;
    }
    if !case["java"].as_str().unwrap().starts_with("structural.") {
        assert_eq!(case["java_errors"], json!([]), "upstream assertions failed");
    }
    let mut rows = case["operations"].as_array().unwrap().clone();
    assert!(!rows.is_empty(), "case requires a native port");
    correct(case["java"].as_str().unwrap(), &mut rows);
    let mut reasoners = HashMap::new();
    let mut assertions = 0;
    for (index, row) in rows.iter().enumerate() {
        eprintln!("{} operation {index}: {}", case["java"], row["op"]);
        match row["op"].as_str().unwrap() {
            "normalize" | "clausify" => {
                java_structural::run(row);
                assertions += 1;
            }
            "create" => {
                assert_eq!(
                    row["description_graphs"], 0,
                    "description graphs require native fixture"
                );
                let mut reasoner = r::IncrementalReasoner::with_configuration(
                    ontology(&row["ontology"]),
                    config(row),
                );
                reasoner.dl_ontology();
                reasoners.insert(row["id"].as_u64().unwrap(), reasoner);
                assertions += 1;
            }
            "invalid" => {
                assert!(
                    std::panic::catch_unwind(|| r::is_ontology_consistent(&ontology(
                        &row["ontology"]
                    )))
                    .map_or(true, |result| result.is_err()),
                    "Java rejected this ontology: {}",
                    row["error"]
                );
                assertions += 1;
            }
            "canProcessPendingChangesIncrementally" => {
                let r = reasoners.get_mut(&row["id"].as_u64().unwrap()).unwrap();
                apply_delta(r, &ontology(&row["ontology"]));
                assert_eq!(
                    r.can_process_pending_changes_incrementally(),
                    row["expected"].as_bool().unwrap()
                );
                assertions += 1;
            }
            "flush" => {
                let r = reasoners.get_mut(&row["id"].as_u64().unwrap()).unwrap();
                apply_delta(r, &ontology(&row["ontology"]));
                r.flush();
            }
            _ => {
                let r = reasoners.get_mut(&row["id"].as_u64().unwrap()).unwrap();
                if row.get("ontology").is_some() {
                    apply_delta(r, &ontology(&row["ontology"]));
                }
                let result = query(r, row);
                if row.get("exception").is_some() {
                    assert!(result.is_err(), "Java expected an exception: {row}");
                    assertions += 1;
                    continue;
                }
                let mut got = result.unwrap();
                let mut want = row["expected"].clone();
                if row["op"] == "printHierarchies" {
                    let expected = parse(want.as_str().unwrap());
                    let text = got.as_str().unwrap();
                    let actual = parse(&format!("{PREFIXES} Ontology({text})"));
                    let axioms = |o: O| -> HashSet<_> {
                        o.into_iter()
                            .filter(|a| !matches!(a.component, Component::OntologyID(_)))
                            .map(|a| {
                                java_structural::canonical(&a.component.as_functional().to_string())
                            })
                            .collect()
                    };
                    assert_eq!(axioms(actual), axioms(expected));
                    assertions += 1;
                    continue;
                }
                normalize(&mut got);
                normalize(&mut want);
                assert_eq!(
                    got, want,
                    "{} operation {index}: {}",
                    case["java"], row["op"]
                );
                assertions += 1;
            }
        }
    }
    assert!(assertions > 0, "case has no assertions");
}
fn isolated_raw(path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    let log = std::env::temp_dir().join(format!(
        "hermit-java-{}-{}.log",
        std::process::id(),
        path.file_stem().unwrap().to_string_lossy()
    ));
    let file = std::fs::File::create(&log)?;
    let mut child = Command::new(std::env::current_exe()?)
        .arg("--case")
        .arg(&path)
        .env("OWLMAKE_CLASSIFY_THREADS", "1")
        .stdout(Stdio::from(file.try_clone()?))
        .stderr(Stdio::from(file))
        .spawn()?;
    let start = Instant::now();
    let status = loop {
        if let Some(s) = child.try_wait()? {
            break Some(s);
        }
        if start.elapsed() > Duration::from_secs(120) {
            child.kill()?;
            child.wait()?;
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let output = std::fs::read_to_string(&log)?;
    std::fs::remove_file(log)?;
    match status {
        Some(status) if status.success() => Ok(()),
        Some(_) => Err(output.into()),
        None => Err(format!("case timed out; {output}").into()),
    }
}
fn isolated(path: PathBuf) -> Result<(), libtest_mimic::Failed> {
    let name = path.file_stem().unwrap().to_str().unwrap();
    java_outcome::check(name, isolated_raw(&path).map_err(|e| e.to_string())).map_err(Into::into)
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.get(1).is_some_and(|a| a == "--case") {
        run_case(Path::new(&args[2]));
        return;
    }
    let mut arguments = libtest_mimic::Arguments::from_args();
    if arguments.test_threads.is_none() {
        arguments.test_threads = Some(1);
    }
    let mut paths: Vec<_> = std::fs::read_dir(Path::new(ROOT).join("cases"))
        .unwrap()
        .map(|p| p.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "json"))
        .collect();
    paths.sort();
    let native: HashMap<String, String> =
        serde_json::from_str(include_str!("java/native-cases.json")).unwrap();
    let disabled: HashMap<String, String> =
        serde_json::from_str(include_str!("java/disabled.json")).unwrap();
    let trials = paths
        .into_iter()
        .filter(|path| !native.contains_key(path.file_stem().unwrap().to_str().unwrap()))
        .map(|path| {
            let name = path.file_stem().unwrap().to_string_lossy().into_owned();
            let ignored = disabled.contains_key(&name);
            let label = if java_outcome::is_known_failure(&name) {
                format!("XFAIL {name}")
            } else {
                name
            };
            libtest_mimic::Trial::test(label, move || isolated(path)).with_ignored_flag(ignored)
        })
        .collect();
    libtest_mimic::run(&arguments, trials).exit();
}

// OWLAPI can serialize empty Boolean constructors and singleton role chains.
// Preserve their meaning when adapting those legacy test objects to the stricter
// Functional Syntax grammar. Tokenization keeps literal contents untouched.
fn java_syntax(src: &str) -> String {
    fn term(tokens: &[&str], at: &mut usize) -> String {
        let name = tokens[*at];
        *at += 1;
        if name != "(" && tokens.get(*at) != Some(&"(") {
            return name.into();
        }
        if name != "(" {
            *at += 1;
        }
        let mut args = Vec::new();
        while tokens.get(*at).is_some_and(|s| *s != ")") {
            args.push(term(tokens, at));
        }
        assert_eq!(tokens.get(*at), Some(&")"));
        *at += 1;
        match (name, args.len()) {
            ("ObjectIntersectionOf", 0) => "<http://www.w3.org/2002/07/owl#Thing>".into(),
            ("ObjectUnionOf" | "ObjectOneOf", 0) => {
                "<http://www.w3.org/2002/07/owl#Nothing>".into()
            }
            ("ObjectIntersectionOf" | "ObjectUnionOf" | "ObjectPropertyChain", 1) => args.remove(0),
            ("(", _) => format!("({})", args.join(" ")),
            _ => format!("{name}({})", args.join(" ")),
        }
    }
    static TOKENIZER: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    let re = TOKENIZER.get_or_init(|| {
        regex::Regex::new(r#""(?:\\.|[^"\\])*"(?:\^\^<[^>]*>|@[\w-]+)?|<[^>]*>|[^\s()]+|[()]"#)
            .unwrap()
    });
    let tokens: Vec<_> = re.find_iter(src).map(|m| m.as_str()).collect();
    let mut at = 0;
    let mut out = Vec::new();
    while at < tokens.len() {
        out.push(term(&tokens, &mut at));
    }
    out.join(" ")
}
