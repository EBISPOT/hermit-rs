//! Issue #21: printing the hierarchies never declares a built-in entity. Every
//! OWL 2 ontology implicitly declares owl:Thing, owl:Nothing,
//! owl:topObjectProperty, owl:bottomObjectProperty, owl:topDataProperty and
//! owl:bottomDataProperty (OWL 2 Structural Specification §5.8, Table 5), so a
//! declaration of one is redundant, and HermiT's `HierarchyPrinterFSS` prints
//! none. The hierarchy of an inconsistent ontology is one node, both its top
//! and its bottom node, which the top element represents. The class printer
//! took the built-in classes to be the representatives of the top and bottom
//! nodes, so it declared owl:Nothing there (`ReasonerTest.testHierarchyPrinting3`),
//! while the property printers compared with the built-in IRIs. In a collapsed
//! hierarchy the bottom element also sorted among the other names, not first.
use hermit_rs::{configuration::*, reasoner, structural::A};
use horned_owl::io::ofn::writer::AsFunctional;
use horned_owl::{model::*, ontology::set::SetOntology};
use std::collections::BTreeSet;

const OWL: &str = "http://www.w3.org/2002/07/owl#";

fn parse(axioms: &str) -> SetOntology<A> {
    let source = format!("Prefix(:=<urn:issue21:>)\nPrefix(owl:=<{OWL}>)\nOntology(\n{axioms}\n)");
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
        .unwrap()
        .0
}

/// The axioms of an ontology in functional syntax, which keeps the order of
/// the members of an equivalence.
fn axioms(ontology: SetOntology<A>) -> BTreeSet<String> {
    ontology
        .into_iter()
        .filter(|a| !matches!(a.component, Component::OntologyID(_)))
        .map(|a| a.component.as_functional().to_string())
        .collect()
}

/// The entities that the printed hierarchies declare, read back as an
/// ontology, as the Java replay reads them.
fn declared(printed: &str) -> BTreeSet<String> {
    parse(printed)
        .into_iter()
        .filter_map(|a| match a.component {
            Component::DeclareClass(DeclareClass(c)) => Some(c.0.to_string()),
            Component::DeclareObjectProperty(DeclareObjectProperty(p)) => Some(p.0.to_string()),
            Component::DeclareDataProperty(DeclareDataProperty(p)) => Some(p.0.to_string()),
            _ => None,
        })
        .collect()
}

/// The entities that the printed hierarchies mention, except the built-in ones.
fn mentioned_entities_not_built_in(printed: &str) -> BTreeSet<String> {
    let built_in = [
        "Thing",
        "Nothing",
        "topObjectProperty",
        "bottomObjectProperty",
        "topDataProperty",
        "bottomDataProperty",
    ]
    .map(|name| format!("{OWL}{name}"));
    printed
        .split('<')
        .skip(1)
        .map(|rest| rest.split('>').next().unwrap().to_string())
        .filter(|iri| !built_in.contains(iri))
        .collect()
}

/// The configurations of the Java suites (the defaults, core blocking and
/// individual reuse), without the exception for an inconsistent ontology, as
/// in `AbstractReasonerTest.getConfiguration`.
fn configurations() -> Vec<Configuration> {
    let base = Configuration {
        throw_inconsistent_ontology_exception: false,
        ..Configuration::default()
    };
    vec![
        base.clone(),
        Configuration {
            blocking_strategy_type: BlockingStrategyType::SimpleCore,
            direct_blocking_type: DirectBlockingType::Single,
            blocking_signature_cache_type: BlockingSignatureCacheType::NotCached,
            ..base.clone()
        },
        Configuration { existential_strategy_type: ExistentialStrategyType::IndividualReuse, ..base },
    ]
}

/// Inconsistent ontologies and their printed hierarchies. An inconsistent
/// ontology entails every axiom, so each hierarchy is one equivalence, with
/// the bottom and top elements first, and only the other entities are
/// declared.
const INCONSISTENT: [(&str, &str); 3] = [
    // The ontology of `ReasonerTest.testHierarchyPrinting3`, with the axioms
    // of `hierarchy-printing-3.txt`.
    (
        "SubClassOf(:A :B) SubClassOf(owl:Thing owl:Nothing)",
        "EquivalentClasses(owl:Nothing owl:Thing :A :B)
         Declaration(Class(:A)) Declaration(Class(:B))
         EquivalentObjectProperties(owl:bottomObjectProperty owl:topObjectProperty)
         EquivalentDataProperties(owl:bottomDataProperty owl:topDataProperty)",
    ),
    // With properties.
    (
        "SubClassOf(:A :B) SubObjectPropertyOf(:r :s) SubDataPropertyOf(:d :e)
         SubClassOf(owl:Thing owl:Nothing)",
        "EquivalentClasses(owl:Nothing owl:Thing :A :B)
         Declaration(Class(:A)) Declaration(Class(:B))
         EquivalentObjectProperties(owl:bottomObjectProperty owl:topObjectProperty :r :s)
         Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s))
         EquivalentDataProperties(owl:bottomDataProperty owl:topDataProperty :d :e)
         Declaration(DataProperty(:d)) Declaration(DataProperty(:e))",
    ),
    // Inconsistent assertions, with inverse roles, which are not declared.
    (
        "InverseObjectProperties(:r :ri) SubObjectPropertyOf(:q ObjectInverseOf(:r))
         DataPropertyAssertion(:d :a \"x\")
         ClassAssertion(:A :a) ClassAssertion(ObjectComplementOf(:A) :a)",
        "EquivalentClasses(owl:Nothing owl:Thing :A) Declaration(Class(:A))
         EquivalentObjectProperties(owl:bottomObjectProperty owl:topObjectProperty :q :r :ri
             ObjectInverseOf(:q) ObjectInverseOf(:r) ObjectInverseOf(:ri))
         Declaration(ObjectProperty(:q)) Declaration(ObjectProperty(:r))
         Declaration(ObjectProperty(:ri))
         EquivalentDataProperties(owl:bottomDataProperty owl:topDataProperty :d)
         Declaration(DataProperty(:d))",
    ),
];

#[test]
fn the_hierarchies_of_an_inconsistent_ontology_declare_no_built_in_entity() {
    for (ontology, expected) in INCONSISTENT {
        let o = parse(ontology);
        for c in configurations() {
            let printed =
                reasoner::print_hierarchies_with_configuration(&o, true, true, true, &c).unwrap();
            assert_eq!(axioms(parse(&printed)), axioms(parse(expected)), "{printed}");
            assert_eq!(declared(&printed), mentioned_entities_not_built_in(&printed), "{printed}");
        }
    }
}

#[test]
fn consistent_hierarchies_declare_no_built_in_entity_either() {
    // The built-in entities share their nodes with other entities.
    let o = parse(
        "SubClassOf(:A :B) SubClassOf(owl:Thing :T) SubClassOf(:G owl:Nothing)
         SubObjectPropertyOf(owl:topObjectProperty :u)
         SubObjectPropertyOf(:e owl:bottomObjectProperty)
         SubDataPropertyOf(:g :h) SubDataPropertyOf(:f owl:bottomDataProperty)",
    );
    let equivalences = axioms(parse(
        "EquivalentClasses(owl:Thing :T) EquivalentClasses(owl:Nothing :G)
         EquivalentObjectProperties(owl:topObjectProperty :u ObjectInverseOf(:u))
         EquivalentObjectProperties(owl:bottomObjectProperty :e ObjectInverseOf(:e))
         EquivalentDataProperties(owl:bottomDataProperty :f)",
    ));
    let names: BTreeSet<String> =
        "A B T G u e g h f".split(' ').map(|name| format!("urn:issue21:{name}")).collect();
    for c in configurations() {
        let printed =
            reasoner::print_hierarchies_with_configuration(&o, true, true, true, &c).unwrap();
        assert!(axioms(parse(&printed)).is_superset(&equivalences), "{printed}");
        assert_eq!(declared(&printed), names, "{printed}");
        assert_eq!(declared(&printed), mentioned_entities_not_built_in(&printed), "{printed}");
    }
}

#[test]
fn a_printed_class_hierarchy_reads_back_as_the_same_hierarchy() {
    // Without the redundant declaration of owl:Nothing, the printed class
    // hierarchy is still an ontology that the reader accepts and whose
    // hierarchy prints the same.
    let consistent = "SubClassOf(:A :B) SubClassOf(:G owl:Nothing)";
    for ontology in INCONSISTENT.map(|(ontology, _)| ontology).into_iter().chain([consistent]) {
        let o = parse(ontology);
        for c in configurations() {
            let print = |o: &SetOntology<A>| {
                reasoner::print_hierarchies_with_configuration(o, true, false, false, &c).unwrap()
            };
            let printed = print(&o);
            assert_eq!(print(&parse(&printed)), printed);
        }
    }
}
