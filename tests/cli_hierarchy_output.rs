//! Two CLI output bugs without an issue.
//!
//! The `-O` hierarchy came from `classify_object_properties`, which projects
//! the object-property-expression hierarchy onto named properties but looked
//! up no subsumers for owl:topObjectProperty. A property equivalent to it then
//! subsumed the top property without being subsumed back, so `-O` printed it
//! below the top node: nothing for the dump, and
//! `SubObjectPropertyOf( :r owl:topObjectProperty )` for `-OP`, instead of
//! `EquivalentObjectProperties( owl:topObjectProperty :r )`.
//!
//! `--prettyPrint` concatenated its sections with no `Prefix(...)` /
//! `Ontology(...)` header, so the output was not an ontology document.
use hermit_rs::cli;
use hermit_rs::structural::A;
use horned_owl::model::Build;

const TOP_OP: &str = "http://www.w3.org/2002/07/owl#topObjectProperty";
const BOTTOM_OP: &str = "http://www.w3.org/2002/07/owl#bottomObjectProperty";
const BOTTOM_DP: &str = "http://www.w3.org/2002/07/owl#bottomDataProperty";
const THING: &str = "http://www.w3.org/2002/07/owl#Thing";

const ONTOLOGY: &str = r#"Prefix(:=<http://example.org/cli#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://example.org/cli>
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
Declaration(ObjectProperty(:empty))
Declaration(DataProperty(:d))
Declaration(DataProperty(:e))
Declaration(DataProperty(:dempty))
Declaration(Class(:A))
Declaration(Class(:B))
EquivalentObjectProperties(:r owl:topObjectProperty)
SubObjectPropertyOf(:s :r)
ObjectPropertyDomain(:empty owl:Nothing)
SubDataPropertyOf(:e :d)
DataPropertyDomain(:dempty owl:Nothing)
EquivalentClasses(:A owl:Thing)
SubClassOf(:B :A)
)"#;

fn ex(name: &str) -> String {
    format!("<http://example.org/cli#{name}>")
}

/// Writes `text` to a fresh file and returns its path.
fn write_temp(name: &str, text: &str) -> String {
    let dir = std::env::temp_dir().join(format!("hermit-cli-output-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path.to_string_lossy().into_owned()
}

fn run(flags: &str, path: &str) -> String {
    cli::run(&[flags.to_string(), path.to_string()]).unwrap()
}

#[test]
fn object_property_equivalent_to_top_is_in_the_top_node() {
    let path = write_temp("top.ofn", ONTOLOGY);
    let top = format!("<{TOP_OP}>");

    let dump = run("-O", &path);
    assert!(
        dump.contains(&format!("EquivalentObjectProperties( {top} {} )", ex("r"))),
        "{dump}"
    );
    assert!(dump.contains(&format!("EquivalentObjectProperties( <{BOTTOM_OP}> {} )", ex("empty"))), "{dump}");
    assert!(!dump.contains(&format!("SubObjectPropertyOf( {} {top} )", ex("r"))), "{dump}");

    let pretty = run("-OP", &path);
    assert!(
        pretty.contains(&format!("EquivalentObjectProperties( {top} {} )", ex("r"))),
        "{pretty}"
    );
    assert!(!pretty.contains(&format!("SubObjectPropertyOf( {} {top} )", ex("r"))), "{pretty}");
    // :s lies directly below the top node, which :r now represents with the
    // top property.
    assert!(pretty.contains(&format!("SubObjectPropertyOf( {} {top} )", ex("s"))), "{pretty}");

    // The library hierarchy the CLI prints groups the two as well.
    let ontology = cli::load_ontology(&path).unwrap();
    let hierarchy = hermit_rs::reasoner::classify_object_properties(&ontology).unwrap();
    let build = Build::<A>::new_arc();
    let r = build.object_property("http://example.org/cli#r");
    assert_eq!(hierarchy.node_for_element(&r), Some(hierarchy.top_node()));
    assert!(hierarchy.node(hierarchy.top_node()).is_equivalent_element(&r));
}

#[test]
fn class_and_data_property_outputs_group_top_and_bottom() {
    let path = write_temp("classes.ofn", ONTOLOGY);
    let classes = run("-c", &path);
    assert!(classes.contains(&format!("EquivalentClasses( <{THING}> {} )", ex("A"))), "{classes}");
    assert!(!classes.contains(&format!("SubClassOf( {} <{THING}> )", ex("A"))), "{classes}");

    let data = run("-D", &path);
    assert!(data.contains(&format!("SubDataPropertyOf( {} {} )", ex("e"), ex("d"))), "{data}");
    let pretty = run("-DP", &path);
    assert!(
        pretty.contains(&format!("EquivalentDataProperties( <{BOTTOM_DP}> {} )", ex("dempty"))),
        "{pretty}"
    );
    assert!(!pretty.contains(&format!("SubDataPropertyOf( {} ", ex("dempty"))), "{pretty}");
}

#[test]
fn pretty_print_is_an_ontology_document_that_round_trips() {
    let path = write_temp("pretty.ofn", ONTOLOGY);
    let pretty = run("-cODP", &path);
    assert!(pretty.starts_with("Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\nOntology(<http://example.org/cli>\n"), "{pretty}");
    assert!(pretty.trim_end().ends_with(')'), "{pretty}");

    // The document parses with the repo's own loader, and holds exactly the
    // printed axioms.
    let printed = write_temp("printed.ofn", &pretty);
    let reparsed = cli::load_ontology(&printed).unwrap();
    let axiom_lines = pretty
        .lines()
        .filter(|line| line.contains("( <") || line.starts_with("Declaration"))
        .count();
    let components = reparsed
        .iter()
        .filter(|c| !matches!(c.component, horned_owl::model::Component::OntologyID(_)))
        .count();
    assert_eq!(components, axiom_lines, "{pretty}");

    // Classifying the printed hierarchy reproduces it.
    let again = run("-cODP", &printed);
    let body = |text: &str| -> Vec<String> {
        let mut lines: Vec<String> =
            text.lines().filter(|l| l.contains("( <")).map(str::to_string).collect();
        lines.sort();
        lines
    };
    assert_eq!(body(&again), body(&pretty));

    // An ontology without an IRI gives an anonymous document.
    let anonymous = write_temp(
        "anonymous.ofn",
        "Prefix(:=<http://example.org/cli#>)\nOntology(\nSubClassOf(:B :A)\n)",
    );
    let pretty = run("-cP", &anonymous);
    assert!(pretty.contains("\nOntology(\n"), "{pretty}");
    cli::load_ontology(&write_temp("anonymous-printed.ofn", &pretty)).unwrap();
}
