//! Issue #19: `getTypes(individual, true)` returns the most specific named
//! classes the individual is entailed to be an instance of: the minimal nodes of
//! the class hierarchy among its types. Under the OWL 2 Direct Semantics the
//! types of an individual are closed under subsumption, so a direct type is a
//! type none of whose strict subclasses is a type, and owl:Thing is a direct
//! type only of an individual with no other type.
//!
//! The instance manager keeps each known instance at the most specific node
//! that records it, and the direct filter compared a known node with its
//! children only. In `ReasonerTest.testDirect`, `:a` is a known instance of
//! owl:Thing and becomes one of `:C` only when `realize` confirms the possible
//! instance that `:D` or `:E` pushes up, so owl:Thing, whose child is `:B`, stayed
//! a direct type beside `:C`. `realize` also visited the nodes breadth-first
//! upward from the bottom node and stopped at nodes without instances, so a
//! possible instance could reach a node already visited, or a node that was
//! never visited, and was never tested. Java tests such leftover possibles when a
//! query reaches them; the Rust queries read the known instances only, so the
//! type was lost, direct or not.
//!
//! Each check compares `getTypes`, `realize` and `getInstances`, direct and not,
//! with separate entailment tests: `C` is a type of `a` when the ontology with
//! `ObjectComplementOf(C)(a)` is inconsistent, and a type is direct when no
//! other type is strictly subsumed by it.
use hermit_rs::{configuration::*, reasoner, structural::A};
use horned_owl::{model::*, ontology::set::SetOntology};
use std::collections::{HashMap, HashSet};

const THING: &str = "http://www.w3.org/2002/07/owl#Thing";
const NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";

fn parse(axioms: &str) -> SetOntology<A> {
    let source = format!(
        r#"Prefix(:=<urn:issue19:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(
{axioms}
)"#
    );
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
        .unwrap()
        .0
}

fn class(name: &str) -> Class<A> {
    match name {
        "Thing" => Build::new_arc().class(THING),
        "Nothing" => Build::new_arc().class(NOTHING),
        _ => Build::new_arc().class(format!("urn:issue19:{name}")),
    }
}

fn classes(names: &[&str]) -> HashSet<Class<A>> {
    names.iter().map(|name| class(name)).collect()
}

fn individual(name: &str) -> NamedIndividual<A> {
    Build::new_arc().named_individual(format!("urn:issue19:{name}"))
}

/// The configurations of the Java suites: the defaults, core blocking and
/// individual reuse.
fn configurations() -> Vec<(&'static str, Configuration)> {
    vec![
        ("the default configuration", Configuration::default()),
        (
            "core blocking",
            Configuration {
                blocking_strategy_type: BlockingStrategyType::SimpleCore,
                direct_blocking_type: DirectBlockingType::Single,
                blocking_signature_cache_type: BlockingSignatureCacheType::NotCached,
                ..Configuration::default()
            },
        ),
        (
            "individual reuse",
            Configuration {
                existential_strategy_type: ExistentialStrategyType::IndividualReuse,
                ..Configuration::default()
            },
        ),
    ]
}

fn is_type(o: &SetOntology<A>, a: &NamedIndividual<A>, c: &Class<A>) -> bool {
    reasoner::is_instance_of(o, a.clone(), ClassExpression::Class(c.clone())).unwrap()
}

fn is_subclass(o: &SetOntology<A>, sub: &Class<A>, sup: &Class<A>) -> bool {
    reasoner::is_subsumed_by(
        o,
        ClassExpression::Class(sub.clone()),
        ClassExpression::Class(sup.clone()),
    )
    .unwrap()
}

/// Checks the instance queries on the ontology of `axioms`, whose classes are
/// `class_names` besides owl:Thing and owl:Nothing, for the individuals
/// `individual_names`, and returns the direct types of each individual.
fn check(
    axioms: &str,
    class_names: &[&str],
    individual_names: &[&'static str],
) -> HashMap<&'static str, HashSet<Class<A>>> {
    let o = parse(axioms);
    let mut signature = classes(class_names);
    signature.extend([class("Thing"), class("Nothing")]);
    let mut types = HashMap::new();
    let mut direct = HashMap::new();
    for &name in individual_names {
        let a = individual(name);
        let all: HashSet<Class<A>> =
            signature.iter().filter(|c| is_type(&o, &a, c)).cloned().collect();
        let minimal: HashSet<Class<A>> = all
            .iter()
            .filter(|c| !all.iter().any(|d| is_subclass(&o, d, c) && !is_subclass(&o, c, d)))
            .cloned()
            .collect();
        types.insert(name, all);
        direct.insert(name, minimal);
    }
    for (label, configuration) in configurations() {
        let realization = reasoner::realize_with_configuration(&o, &configuration).unwrap();
        for &name in individual_names {
            let a = individual(name);
            let context = format!("{name} under {label}");
            let get_types = |only_direct| {
                reasoner::get_types_with_configuration(&o, &a, only_direct, &configuration).unwrap()
            };
            assert_eq!(get_types(false), types[name], "types of {context}");
            assert_eq!(get_types(true), direct[name], "direct types of {context}");
            assert_eq!(realization[&a], direct[name], "realization of {context}");
            // Equivalent direct types form one node.
            let nodes =
                reasoner::type_nodes_with_configuration(&o, &a, true, &configuration).unwrap();
            for node in nodes.iter() {
                for c in node.entities() {
                    for d in &direct[name] {
                        assert_eq!(
                            node.contains(d),
                            is_subclass(&o, c, d) && is_subclass(&o, d, c),
                            "direct type nodes of {context}"
                        );
                    }
                }
            }
            assert_eq!(nodes.flattened(), direct[name], "direct type nodes of {context}");
        }
        for c in &signature {
            let instances = |of: &HashMap<&str, HashSet<Class<A>>>| -> HashSet<NamedIndividual<A>> {
                individual_names
                    .iter()
                    .filter(|&&name| of[name].contains(c))
                    .map(|name| individual(name))
                    .collect()
            };
            let context = format!("{} under {label}", c.0);
            let get_instances = |only_direct| {
                reasoner::instances_with_configuration(&o, c, only_direct, &configuration).unwrap()
            };
            assert_eq!(get_instances(false), instances(&types), "instances of {context}");
            assert_eq!(get_instances(true), instances(&direct), "direct instances of {context}");
        }
    }
    direct
}

/// `ReasonerTest.testDirect`: `:a` is a `:C` by either disjunct of each
/// assertion, since `:Cp` is empty and `:D` and `:E` are subclasses of `:C`, but
/// neither `:D` nor `:E` is entailed.
#[test]
fn most_specific_type_below_intervening_class() {
    let direct = check(
        "SubClassOf(:F :A)
SubClassOf(:C :B)
SubClassOf(:D :C)
SubClassOf(:E :C)
SubClassOf(:Cp owl:Nothing)
ClassAssertion(ObjectUnionOf(:D :E) :a)
ClassAssertion(ObjectUnionOf(:C :Cp) :a)",
        &["A", "B", "C", "Cp", "D", "E", "F"],
        &["a"],
    );
    assert_eq!(direct["a"], classes(&["C"]));
}

/// `:a` is a known `:A` and becomes a `:D`, three levels below `:A`, only when
/// the possible instance of `:F1` or `:F2` is pushed up. The pinned Java
/// checkout returns both `:A` and `:D` here: its breadth-first `getTypes`
/// reaches the known `:A` from its leaf `:G` before it confirms `:D`.
#[test]
fn known_type_above_deeper_confirmed_type() {
    let direct = check(
        "SubClassOf(:G :A)
SubClassOf(:D2 :A)
SubClassOf(:D1 :D2)
SubClassOf(:D :D1)
SubClassOf(:E1 :D)
SubClassOf(:E2 :D)
SubClassOf(:F1 :E1)
SubClassOf(:F2 :E2)
ClassAssertion(:A :a)
ClassAssertion(ObjectUnionOf(:F1 :F2) :a)",
        &["A", "D", "D1", "D2", "E1", "E2", "F1", "F2", "G"],
        &["a"],
    );
    assert_eq!(direct["a"], classes(&["D"]));
}

/// A possible instance refuted along a chain of three classes reaches `:P`
/// after `:P` was reached from `:Y`, one level up; either disjunct makes `:a` a
/// `:P`.
#[test]
fn possible_instance_pushed_up_a_longer_path() {
    let direct = check(
        "SubClassOf(:X3 :X2)
SubClassOf(:X2 :X)
SubClassOf(:X :P)
SubClassOf(:Z3 :Z2)
SubClassOf(:Z2 :Z)
SubClassOf(:Z :P)
SubClassOf(:Y :P)
ClassAssertion(ObjectUnionOf(:X3 :Z3) :a)
ClassAssertion(:Y :b)",
        &["P", "X", "X2", "X3", "Y", "Z", "Z2", "Z3"],
        &["a", "b"],
    );
    assert_eq!(direct["a"], classes(&["P"]));
    assert_eq!(direct["b"], classes(&["Y"]));
}

/// `:a` is a possible instance of `:B`, whose subclass `:C` records no
/// instance, so an upward traversal that stops at nodes without instances never
/// reaches `:B`; either disjunct makes `:a` a `:B`.
#[test]
fn possible_instance_above_classes_without_instances() {
    let direct = check(
        "SubClassOf(:C :B)
SubClassOf(ObjectSomeValuesFrom(:r :X) :B)
SubClassOf(ObjectSomeValuesFrom(:s :Y) :B)
ClassAssertion(ObjectUnionOf(ObjectSomeValuesFrom(:r :X) ObjectSomeValuesFrom(:s :Y)) :a)",
        &["B", "C", "X", "Y"],
        &["a"],
    );
    assert_eq!(direct["a"], classes(&["B"]));
}

/// owl:Thing and the classes equivalent to it are the direct types of an
/// individual with no other type, and no direct type of the others; an
/// unsatisfiable class, equivalent to owl:Nothing, is never a type.
#[test]
fn thing_and_nothing() {
    let direct = check(
        "EquivalentClasses(:T owl:Thing)
SubClassOf(:U owl:Nothing)
SubClassOf(:C :B)
ClassAssertion(ObjectUnionOf(:C :U) :a)
ClassAssertion(ObjectUnionOf(:B :U) :b)
Declaration(NamedIndividual(:c))",
        &["B", "C", "T", "U"],
        &["a", "b", "c"],
    );
    assert_eq!(direct["a"], classes(&["C"]));
    assert_eq!(direct["b"], classes(&["B"]));
    assert_eq!(direct["c"], classes(&["T", "Thing"]));
}

/// Equivalent classes form one direct type, incomparable types are each direct,
/// a subclass of two classes hides both, and a disjunction of two classes gives
/// their most specific common superclass.
#[test]
fn equivalent_and_incomparable_types() {
    let direct = check(
        "EquivalentClasses(:C :C2)
SubClassOf(:C :B1)
SubClassOf(:D :B1)
SubClassOf(:D :B2)
SubClassOf(:B1 :A)
SubClassOf(:B2 :A)
SubClassOf(:E1 :C)
SubClassOf(:E2 :C)
ClassAssertion(ObjectUnionOf(:E1 :E2) :a)
ClassAssertion(:D :b)
ClassAssertion(ObjectIntersectionOf(:B1 :B2) :c)
ClassAssertion(ObjectUnionOf(:D :C) :d)",
        &["A", "B1", "B2", "C", "C2", "D", "E1", "E2"],
        &["a", "b", "c", "d"],
    );
    assert_eq!(direct["a"], classes(&["C", "C2"]));
    assert_eq!(direct["b"], classes(&["D"]));
    assert_eq!(direct["c"], classes(&["B1", "B2"]));
    assert_eq!(direct["d"], classes(&["B1"]));
}

/// Types forced through equality: `:b` is the same as `:a`, and `:n` is the
/// only instance of `:N`, which makes `:N` a subclass of `:M`.
#[test]
fn types_through_equality_and_nominals() {
    let direct = check(
        "SameIndividual(:a :b)
SubClassOf(:D :C)
SubClassOf(:E :C)
ClassAssertion(ObjectUnionOf(:D :E) :a)
EquivalentClasses(:N ObjectOneOf(:n))
SubClassOf(:N :C)
ClassAssertion(:M :n)",
        &["C", "D", "E", "M", "N"],
        &["a", "b", "n"],
    );
    assert_eq!(direct["a"], classes(&["C"]));
    assert_eq!(direct["b"], classes(&["C"]));
    assert_eq!(direct["n"], classes(&["N"]));
}
