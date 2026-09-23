// Lazy unfolding of acyclic definitorial TBoxes for consistency checks.
//
// Not a HermiT port. HermiT clausifies both directions of a definition
// `A ≡ E`; the `E ⊑ A` direction becomes a disjunction on every node (for
// example `A ∨ B ∨ ¬C` when `E = ¬B ⊓ C`) or on every edge (`A(x) ∨ C(y)` when
// `E = ∃R.¬C`). On ontologies made of such definitions plus an ABox, like the
// DL98 k_poly benchmark (WebOnt description-logic-208/209), this makes the
// search exponential: Java HermiT times out on them as well.
//
// When the ontology consists only of definitions `A ≡ E` of distinct named
// classes whose definitions are acyclic, plus class and object-property
// assertions, satisfiability is decided by lazy unfolding instead: each defined
// `A` gets a fresh complement name `notA`, and the ontology is replaced by
//
//   A ⊑ nnf(E)     notA ⊑ nnf(¬E)     A ⊓ notA ⊑ ⊥
//
// with every class expression in negation normal form and every `¬A` of a
// defined `A` replaced by `notA`. Both ontologies are equisatisfiable. A model of
// the original one is a model of the new one when `notA` is read as `¬A`.
// Conversely, given a model `I'` of the new one, keep the primitive classes and
// the roles, and define each `A` as `E`, in definition order (the definitions
// are acyclic). By induction on the definition depth and the expression size,
// every expression `F` in the new ontology satisfies `F^I' ⊆ F*^I`, where `F*`
// reads `notA` as `¬A`: for `A`, `A^I' ⊆ nnf(E)^I' ⊆ E^I = A^I`; for `notA`,
// `notA^I' ⊆ nnf(¬E)^I' ⊆ (¬E)^I = (¬A)^I`; every other constructor is monotone.
// So `I` satisfies the definitions by construction and every assertion `C(a)`.
//
// Only satisfiability is preserved, not the entailed subsumptions or types, so
// this is applied to whole-ontology consistency checks only.

use std::collections::{BTreeMap, BTreeSet};

use horned_owl::model::{
    Build, Class, ClassAssertion, ClassExpression as CE, Component, DisjointClasses,
    EquivalentClasses, Individual, MutableOntology, ObjectProperty, ObjectPropertyAssertion,
    ObjectPropertyExpression as OPE, SubClassOf,
};
use horned_owl::ontology::set::SetOntology;

use super::A;

/// Prefix of the fresh complement class names. An ontology that already uses
/// such a name is left alone.
const COMPLEMENT_PREFIX: &str = "urn:hermit-rs:definitorial-complement:";

/// Returns an equisatisfiable ontology with the definitions lazily unfolded
/// (see the module comment), or `None` when `ontology` is not made only of
/// acyclic definitions and assertions, or has no definition.
pub fn unfold_definitions(ontology: &SetOntology<A>) -> Option<SetOntology<A>> {
    let mut definitions: BTreeMap<Class<A>, CE<A>> = BTreeMap::new();
    let mut assertions: Vec<Component<A>> = Vec::new();
    for annotated in ontology.iter() {
        match &annotated.component {
            Component::OntologyID(_)
            | Component::OntologyAnnotation(_)
            | Component::AnnotationAssertion(_)
            | Component::DeclareClass(_)
            | Component::DeclareObjectProperty(_)
            | Component::DeclareNamedIndividual(_)
            | Component::DeclareAnnotationProperty(_) => {}
            Component::EquivalentClasses(EquivalentClasses(operands)) => {
                let (defined, definition) = match operands.as_slice() {
                    [CE::Class(c), e] if !is_built_in(c) => (c, e),
                    [e, CE::Class(c)] if !is_built_in(c) => (c, e),
                    _ => return None,
                };
                if !is_supported(definition)
                    || definitions
                        .insert(defined.clone(), definition.clone())
                        .is_some()
                {
                    return None;
                }
            }
            Component::ClassAssertion(ClassAssertion {
                ce,
                i: Individual::Named(_),
            }) if is_supported(ce) => {
                assertions.push(annotated.component.clone());
            }
            Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
                ope: OPE::ObjectProperty(p),
                from: Individual::Named(_),
                to: Individual::Named(_),
            }) if !is_built_in_property(p) => {
                assertions.push(annotated.component.clone());
            }
            _ => return None,
        }
    }
    if definitions.is_empty() || !is_acyclic(&definitions) {
        return None;
    }
    let mut names = BTreeSet::new();
    for (defined, definition) in &definitions {
        names.insert(defined.clone());
        collect_classes(definition, &mut names);
    }
    for assertion in &assertions {
        if let Component::ClassAssertion(ClassAssertion { ce, .. }) = assertion {
            collect_classes(ce, &mut names);
        }
    }
    if names
        .iter()
        .any(|c| c.0.as_ref().starts_with(COMPLEMENT_PREFIX))
    {
        return None;
    }

    let build = Build::new_arc();
    let unfolding = Unfolding {
        definitions: &definitions,
        build: &build,
    };
    let mut unfolded = SetOntology::new();
    for (defined, definition) in &definitions {
        let complement = unfolding.complement(defined);
        unfolded.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(defined.clone()),
            sup: unfolding.nnf(definition, false),
        }));
        unfolded.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(complement.clone()),
            sup: unfolding.nnf(definition, true),
        }));
        unfolded.insert(Component::DisjointClasses(DisjointClasses(vec![
            CE::Class(defined.clone()),
            CE::Class(complement),
        ])));
    }
    for assertion in assertions {
        unfolded.insert(match assertion {
            Component::ClassAssertion(ClassAssertion { ce, i }) => {
                Component::ClassAssertion(ClassAssertion {
                    ce: unfolding.nnf(&ce, false),
                    i,
                })
            }
            other => other,
        });
    }
    Some(unfolded)
}

fn is_built_in(class: &Class<A>) -> bool {
    class.is_thing() || class.is_nothing()
}

fn is_built_in_property(property: &ObjectProperty<A>) -> bool {
    matches!(
        property.0.as_ref(),
        "http://www.w3.org/2002/07/owl#topObjectProperty"
            | "http://www.w3.org/2002/07/owl#bottomObjectProperty"
    )
}

/// Whether `ce` uses only the ALC constructors over named object properties.
fn is_supported(ce: &CE<A>) -> bool {
    match ce {
        CE::Class(_) => true,
        CE::ObjectIntersectionOf(operands) | CE::ObjectUnionOf(operands) => {
            operands.iter().all(is_supported)
        }
        CE::ObjectComplementOf(operand) => is_supported(operand),
        CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(p),
            bce,
        }
        | CE::ObjectAllValuesFrom {
            ope: OPE::ObjectProperty(p),
            bce,
        } => !is_built_in_property(p) && is_supported(bce),
        _ => false,
    }
}

fn collect_classes(ce: &CE<A>, out: &mut BTreeSet<Class<A>>) {
    match ce {
        CE::Class(c) => {
            out.insert(c.clone());
        }
        CE::ObjectIntersectionOf(operands) | CE::ObjectUnionOf(operands) => {
            operands.iter().for_each(|o| collect_classes(o, out));
        }
        CE::ObjectComplementOf(operand) => collect_classes(operand, out),
        CE::ObjectSomeValuesFrom { bce, .. } | CE::ObjectAllValuesFrom { bce, .. } => {
            collect_classes(bce, out)
        }
        _ => {}
    }
}

/// Whether no defined class depends on itself through the definitions.
fn is_acyclic(definitions: &BTreeMap<Class<A>, CE<A>>) -> bool {
    // 0 = unvisited, 1 = on the current path, 2 = done.
    fn visit(
        class: &Class<A>,
        definitions: &BTreeMap<Class<A>, CE<A>>,
        state: &mut BTreeMap<Class<A>, u8>,
    ) -> bool {
        match state.get(class).copied().unwrap_or(0) {
            1 => return false,
            2 => return true,
            _ => {}
        }
        state.insert(class.clone(), 1);
        let mut used = BTreeSet::new();
        collect_classes(&definitions[class], &mut used);
        for next in used.iter().filter(|c| definitions.contains_key(*c)) {
            if !visit(next, definitions, state) {
                return false;
            }
        }
        state.insert(class.clone(), 2);
        true
    }
    let mut state = BTreeMap::new();
    definitions
        .keys()
        .all(|class| visit(class, definitions, &mut state))
}

struct Unfolding<'a> {
    definitions: &'a BTreeMap<Class<A>, CE<A>>,
    build: &'a Build<A>,
}

impl Unfolding<'_> {
    fn complement(&self, class: &Class<A>) -> Class<A> {
        self.build
            .class(format!("{COMPLEMENT_PREFIX}{}", class.0.as_ref()))
    }

    /// The negation normal form of `ce` (of `¬ce` when `negated`), with the
    /// negation of a defined class replaced by its complement name.
    fn nnf(&self, ce: &CE<A>, negated: bool) -> CE<A> {
        match ce {
            CE::Class(c) if c.is_thing() || c.is_nothing() => {
                if c.is_thing() != negated {
                    CE::Class(self.build.class("http://www.w3.org/2002/07/owl#Thing"))
                } else {
                    CE::Class(self.build.class("http://www.w3.org/2002/07/owl#Nothing"))
                }
            }
            CE::Class(c) if !negated => CE::Class(c.clone()),
            CE::Class(c) if self.definitions.contains_key(c) => CE::Class(self.complement(c)),
            CE::Class(c) => CE::ObjectComplementOf(Box::new(CE::Class(c.clone()))),
            CE::ObjectComplementOf(operand) => self.nnf(operand, !negated),
            CE::ObjectIntersectionOf(operands) | CE::ObjectUnionOf(operands) => {
                let operands = operands.iter().map(|o| self.nnf(o, negated)).collect();
                if matches!(ce, CE::ObjectIntersectionOf(_)) != negated {
                    CE::ObjectIntersectionOf(operands)
                } else {
                    CE::ObjectUnionOf(operands)
                }
            }
            CE::ObjectSomeValuesFrom { ope, bce } | CE::ObjectAllValuesFrom { ope, bce } => {
                let ope = ope.clone();
                let bce = Box::new(self.nnf(bce, negated));
                if matches!(ce, CE::ObjectSomeValuesFrom { .. }) != negated {
                    CE::ObjectSomeValuesFrom { ope, bce }
                } else {
                    CE::ObjectAllValuesFrom { ope, bce }
                }
            }
            // `is_supported` admits no other constructor.
            _ => unreachable!("unsupported class expression in a definitorial TBox"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ontology(axioms: &str) -> SetOntology<A> {
        let source = format!(
            "Prefix(:=<http://example.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
             Ontology(<http://example.org/o>\n{axioms}\n)"
        );
        let build = Build::new_arc();
        let (ontology, _): (SetOntology<A>, _) =
            horned_owl::io::ofn::reader::read_with_build(&mut source.as_bytes(), &build).unwrap();
        ontology
    }

    fn consistent(axioms: &str) -> bool {
        let ontology = ontology(axioms);
        assert!(
            unfold_definitions(&ontology).is_some(),
            "not unfolded: {axioms}"
        );
        crate::reasoner::is_ontology_consistent(&ontology).unwrap()
    }

    #[test]
    fn negated_definitions_keep_their_consequences() {
        // `¬A` must still force `¬E`, through both a conjunction and an existential.
        assert!(!consistent(
            "EquivalentClasses(:A ObjectIntersectionOf(:B :C))
             ClassAssertion(:B :a) ClassAssertion(:C :a)
             ClassAssertion(ObjectComplementOf(:A) :a)"
        ));
        assert!(!consistent(
            "EquivalentClasses(:A ObjectSomeValuesFrom(:r ObjectComplementOf(:D)))
             EquivalentClasses(:D ObjectIntersectionOf(:B :C))
             ObjectPropertyAssertion(:r :a :b) ClassAssertion(ObjectComplementOf(:B) :b)
             ClassAssertion(ObjectComplementOf(:A) :a)"
        ));
        assert!(!consistent(
            "EquivalentClasses(:A ObjectAllValuesFrom(:r :B))
             ClassAssertion(:A :a) ObjectPropertyAssertion(:r :a :b)
             ClassAssertion(ObjectComplementOf(:B) :b)"
        ));
        assert!(consistent(
            "EquivalentClasses(:A ObjectSomeValuesFrom(:r ObjectComplementOf(:D)))
             EquivalentClasses(:D ObjectIntersectionOf(:B :C))
             ObjectPropertyAssertion(:r :a :b) ClassAssertion(:B :b)
             ClassAssertion(ObjectComplementOf(:A) :a)"
        ));
        assert!(consistent(
            "EquivalentClasses(:A ObjectUnionOf(:B owl:Nothing))
             ClassAssertion(ObjectComplementOf(:A) :a) ClassAssertion(:C :a)"
        ));
    }

    #[test]
    fn only_acyclic_definitorial_ontologies_are_unfolded() {
        let unfolded = |axioms| unfold_definitions(&ontology(axioms)).is_some();
        assert!(unfolded("EquivalentClasses(:A :B) ClassAssertion(:A :a)"));
        // A cycle, a second definition, a general axiom or a non-ALC
        // constructor keeps the ontology unchanged.
        assert!(!unfolded(
            "EquivalentClasses(:A ObjectSomeValuesFrom(:r :B)) EquivalentClasses(:B :A)"
        ));
        assert!(!unfolded(
            "EquivalentClasses(:A :B) EquivalentClasses(:A :C)"
        ));
        assert!(!unfolded("EquivalentClasses(:A :B) SubClassOf(:C :A)"));
        assert!(!unfolded(
            "EquivalentClasses(:A ObjectMinCardinality(2 :r))"
        ));
        assert!(!unfolded(
            "EquivalentClasses(:A ObjectSomeValuesFrom(ObjectInverseOf(:r) :B))"
        ));
        assert!(!unfolded("EquivalentClasses(:A :B :C)"));
        assert!(!unfolded("ClassAssertion(:A :a)"));
    }
}
