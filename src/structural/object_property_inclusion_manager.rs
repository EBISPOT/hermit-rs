// Port of org.semanticweb.HermiT.structural.ObjectPropertyInclusionManager.
//
// HermiT handles complex object-property inclusions (transitivity and role
// chains) by, for every (non-simple) property R, building a finite automaton
// whose language is exactly the set of role chains implied to be sub-roles of
// R, and then rewriting every `∀R.C` restriction into a set of per-automaton-
// state concept inclusions. This is the standard regular-RIA encoding
// (Horrocks/Kutz/Sattler): transitivity and chains never materialise role
// edges; instead the universal restrictions are pushed along the automaton.
//
// SCOPE. The upstream construction also threads inverse roles through the
// automata (mirrored copies, `increaseAutomatonWithInversePropertyAutomaton`,
// symmetric/equivalent-role handling). That machinery only changes behaviour
// when the role box itself contains inverse/symmetric/equivalent object-
// property *inclusions*; in their absence HermiT's automata reduce to the
// forward construction ported here, and the two agree on the accepted
// language (which is all that the `∀`-rewriting depends on). We therefore port
// the forward fragment faithfully. Several cases beyond the bare forward
// fragment are handled soundly: `∀Inv(R).C` over a complex R (its automaton is
// the mirror of R's, matching `finalizeConstruction`); *symmetric* properties
// (r ⊑ Inv(r)) and *genuine inverse inclusions* (r ⊑ Inv(s)) over simple roles
// -- clausified directly as role-inclusion clauses materialising the edge
// directions; and role chains containing an inverse of a *simple* property
// (e.g. p ∘ Inv(q) ⊑ r). When q is simple the `Inv(q)`-labelled transition
// becomes a `∀Inv(q).D` clause the clausifier already handles; when q is
// *complex*, `buildCompleteAutomataForProperties`'s inverse branch substitutes
// the mirror of q's automaton (`getMirroredCopy`) into the transition.
// Equivalent properties share an automaton (each equivalent of a complex
// property is given a clone, its inverse the mirror -- `individualAutomataFor
// EquivRoles`). A chain inclusion with an inverse *super*-property
// (S1∘...∘Sn ⊑ Inv(r)) is passed through unchanged exactly as Java does: the
// individual automaton is keyed on the anonymous super `Inv(r)`, and the
// mirror-fill / inverse passes derive the named `r`. Genuine inverse simple
// inclusions touching a complex property (r ⊑ Inv(s)) are clausified directly,
// materialising the inverse edges that feed the complex property's automaton.
// The full role-box machinery is thus covered; the only errors are genuine
// OWL 2 DL violations (a non-simple property in a number/Self restriction, an
// irregular role hierarchy) which HermiT also rejects.

use std::collections::{HashMap, HashSet};

use horned_owl::model::{Build, ClassExpression as CE, Individual};

use crate::graph::Graph;

use super::automaton::{
    automata_connector, mirrored_copy, Automaton,
};
use super::owl_axioms::Fact;
use super::{
    inverse_property, is_anonymous_property, ClassExpr, ExpressionManager, ObjectPropExpr,
    OWLAxioms,
};

const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";

/// A canonical, run-stable ordering key for an object-property expression.
///
/// HermiT's role-automaton construction (`ObjectPropertyInclusionManager`) keeps
/// its working automata in `java.util.HashMap`/`HashSet`s and is *order-sensitive*:
/// `automataConnector` disjoint-unions states on every inverse-enrichment, so the
/// automaton a property ends up with depends on the order in which the maps are
/// iterated. Java's hashing is content-based and unseeded, so that order is stable
/// across runs and the construction is reproducible; Rust's `RandomState` reseeds
/// per process, so the unsorted iteration produced a *different* automaton each run
/// (under-enriched -> incomplete, or over-enriched -> unsound). We therefore iterate
/// every such collection in this fixed order, which makes the construction
/// deterministic and confluent. Named properties sort before their inverses, then
/// by IRI -- a total order on the property expressions actually built.
fn prop_sort_key(ope: &ObjectPropExpr) -> (u8, String) {
    use horned_owl::model::ObjectPropertyExpression as OPE;
    match ope {
        OPE::ObjectProperty(p) => (0, p.0.to_string()),
        OPE::InverseObjectProperty(p) => (1, p.0.to_string()),
    }
}

/// Java `String.hashCode()` over UTF-16 code units.
fn java_string_hash(s: &str) -> i32 {
    let mut h: i32 = 0;
    for u in s.encode_utf16() {
        h = h.wrapping_mul(31).wrapping_add(u as i32);
    }
    h
}

/// OWLAPI `IRI.hashCode()` = prefix.hashCode() + remainder.hashCode(), splitting the
/// IRI at the last '#'/'/' (the NCName boundary for OBO/EFO IRIs).
fn owlapi_iri_hash(iri: &str) -> i32 {
    let split = iri.rfind(|c| c == '#' || c == '/').map(|i| i + 1).unwrap_or(0);
    java_string_hash(&iri[..split]).wrapping_add(java_string_hash(&iri[split..]))
}

/// OWLAPI `OWLObjectPropertyExpression.hashCode()`. Reverse-engineered from the
/// bundled OWLAPI: a named property hashes to `IRI.hashCode() + 128743`, and an
/// inverse to the named hash `+ 131471`.
fn owlapi_prop_hash(ope: &ObjectPropExpr) -> i32 {
    use horned_owl::model::ObjectPropertyExpression as OPE;
    match ope {
        OPE::ObjectProperty(p) => owlapi_iri_hash(&p.0.to_string()).wrapping_add(128743),
        OPE::InverseObjectProperty(p) => {
            owlapi_iri_hash(&p.0.to_string()).wrapping_add(128743).wrapping_add(131471)
        }
    }
}

/// The `java.util.HashMap` table capacity holding `n` entries (default 16, doubling
/// whenever `0.75 * capacity` would be below the entry count).
fn java_hashmap_capacity(n: usize) -> usize {
    let mut cap = 16usize;
    while (cap as f64) * 0.75 < n as f64 {
        cap <<= 1;
    }
    cap
}

/// A `java.util.HashMap` iteration-order key for `ope` among a collection of `n`
/// entries: HermiT's automaton maps are `HashMap`s, iterated in bucket order
/// `spread(hash) & (capacity-1)`. The construction is order-sensitive, so to match
/// HermiT bit-for-bit we iterate in this order. `prop_sort_key` breaks bucket
/// collisions deterministically (Java orders those by insertion; collisions are
/// absent in the role boxes we target, and the tiebreak keeps us deterministic).
fn java_map_order_key(ope: &ObjectPropExpr, n: usize) -> (i32, u8, String) {
    let h = owlapi_prop_hash(ope);
    let spread = h ^ ((h as u32 >> 16) as i32);
    let bucket = spread & (java_hashmap_capacity(n) as i32 - 1);
    let (tag, iri) = prop_sort_key(ope);
    (bucket, tag, iri)
}

pub struct ObjectPropertyInclusionManager {
    automata_by_property: HashMap<ObjectPropExpr, Automaton>,
    build: Build<super::A>,
    expression_manager: ExpressionManager,
}

impl ObjectPropertyInclusionManager {
    /// Mirrors `new ObjectPropertyInclusionManager(axioms)`: builds the
    /// per-property automata and records which properties are non-simple in
    /// `axioms.complex_object_property_expressions`.
    pub fn new(axioms: &mut OWLAxioms) -> Result<ObjectPropertyInclusionManager, String> {
        let mut automata_by_property: HashMap<ObjectPropExpr, Automaton> = HashMap::new();
        create_automata(&mut automata_by_property, axioms)?;
        Ok(ObjectPropertyInclusionManager {
            automata_by_property,
            build: Build::new_arc(),
            expression_manager: ExpressionManager::new(),
        })
    }

    fn fresh_class(&self, index: usize) -> ClassExpr {
        CE::Class(self.build.class(format!("internal:all#{}", index)))
    }

    fn complement(&self, ce: &ClassExpr) -> ClassExpr {
        self.expression_manager.get_complement_nnf(ce)
    }

    /// Port of `rewriteNegativeObjectPropertyAssertions`: a negative object
    /// property assertion `¬R(a,b)` over a *complex* R cannot be stored as a
    /// role fact (transitivity rewriting must apply to it), so it becomes
    /// `def(a)`, `nom_b(b)` and `¬def ⊑ ∀R.¬nom_b`.
    pub fn rewrite_negative_object_property_assertions(
        &self,
        axioms: &mut OWLAxioms,
        mut replacement_index: usize,
    ) -> usize {
        let complex = &axioms.complex_object_property_expressions;
        let mut additional_facts: Vec<Fact> = Vec::new();
        let mut retained_facts: Vec<Fact> = Vec::new();
        for fact in std::mem::take(&mut axioms.facts) {
            match &fact {
                Fact::NegativeObjectPropertyAssertion { ope, from, to }
                    if complex.contains(ope) =>
                {
                    let to_iri = match to {
                        Individual::Named(n) => n.0.to_string(),
                        // Negative object property assertions cannot contain
                        // anonymous individuals (OWL 2 structural restriction).
                        Individual::Anonymous(a) => a.0.to_string(),
                    };
                    let individual_concept =
                        CE::Class(self.build.class(format!("internal:nom#{}", to_iri)));
                    let not_individual_concept =
                        CE::ObjectComplementOf(Box::new(individual_concept.clone()));
                    let all_not_individual_concept = CE::ObjectAllValuesFrom {
                        ope: ope.clone(),
                        bce: Box::new(not_individual_concept),
                    };
                    let definition =
                        CE::Class(self.build.class(format!("internal:def#{}", replacement_index)));
                    replacement_index += 1;
                    axioms.concept_inclusions.push(vec![
                        CE::ObjectComplementOf(Box::new(definition.clone())),
                        all_not_individual_concept,
                    ]);
                    additional_facts.push(Fact::ClassAssertion {
                        class_expression: definition,
                        individual: from.clone(),
                    });
                    additional_facts.push(Fact::ClassAssertion {
                        class_expression: individual_concept,
                        individual: to.clone(),
                    });
                    // drop (redundant) the negative assertion
                }
                _ => retained_facts.push(fact),
            }
        }
        retained_facts.extend(additional_facts);
        axioms.facts = retained_facts;
        replacement_index
    }

    /// Port of `rewriteAxioms`: replaces every `∀R.C` whose property has an
    /// automaton with a fresh atomic concept, and emits the concept inclusions
    /// encoding the automaton's states, transitions and final states.
    pub fn rewrite_axioms(
        &self,
        axioms: &mut OWLAxioms,
        mut first_replacement_index: usize,
    ) -> Result<(), String> {
        let complex = &axioms.complex_object_property_expressions;
        // Simplicity checks: a non-simple property may not occur in cardinality
        // restrictions, Self restrictions, or asymmetry/irreflexivity/disjoint
        // property axioms.
        for ope in &axioms.asymmetric_object_properties {
            if complex.contains(ope) {
                return Err(format!("Non-simple property '{:?}' appears in an asymmetric object property axiom.", ope));
            }
        }
        for ope in &axioms.irreflexive_object_properties {
            if complex.contains(ope) {
                return Err(format!("Non-simple property '{:?}' appears in an irreflexive object property axiom.", ope));
            }
        }
        for properties in &axioms.disjoint_object_properties {
            for ope in properties {
                if complex.contains(ope) {
                    return Err(format!("Non-simple property '{:?}' appears in a disjoint object properties axiom.", ope));
                }
            }
        }

        // Replace the `∀R.C` occurrences (collecting one replacement per
        // distinct restriction) and check simple-property usage.
        let mut replaced_descriptions: HashMap<ClassExpr, ClassExpr> = HashMap::new();
        // Preserve discovery order for deterministic clause generation.
        let mut replacement_order: Vec<ClassExpr> = Vec::new();
        for inclusion in &mut axioms.concept_inclusions {
            for class_expression in inclusion.iter_mut() {
                match class_expression {
                    CE::ObjectMinCardinality { ope, .. }
                    | CE::ObjectMaxCardinality { ope, .. }
                    | CE::ObjectExactCardinality { ope, .. } => {
                        if complex.contains(ope) {
                            return Err(format!("Non-simple property '{:?}' appears in a cardinality restriction.", ope));
                        }
                    }
                    CE::ObjectHasSelf(ope) => {
                        if complex.contains(ope) {
                            return Err(format!("Non-simple property '{:?}' appears in a Self restriction.", ope));
                        }
                    }
                    _ => {}
                }
                let all_values_match = match class_expression {
                    CE::ObjectAllValuesFrom { ope, bce } => {
                        if !is_owl_thing(bce) && self.automata_by_property.contains_key(ope) {
                            Some((
                                matches!(&**bce, CE::ObjectComplementOf(_)) || is_owl_nothing(bce),
                            ))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some((filler_is_negative,)) = all_values_match {
                    let key = class_expression.clone();
                    let replacement = if let Some(r) = replaced_descriptions.get(&key) {
                        r.clone()
                    } else {
                        let mut replacement = self.fresh_class(first_replacement_index);
                        first_replacement_index += 1;
                        if filler_is_negative {
                            replacement = self.complement(&replacement);
                        }
                        replaced_descriptions.insert(key.clone(), replacement.clone());
                        replacement_order.push(key.clone());
                        replacement
                    };
                    *class_expression = replacement;
                }
            }
        }

        // Generate the concept inclusions for each replaced restriction.
        for all_values in replacement_order {
            let (property, filler) = match &all_values {
                CE::ObjectAllValuesFrom { ope, bce } => (ope.clone(), (**bce).clone()),
                _ => unreachable!(),
            };
            let replacement_value = replaced_descriptions[&all_values].clone();
            let automaton = &self.automata_by_property[&property];
            let is_of_negative_polarity = matches!(replacement_value, CE::ObjectComplementOf(_));

            // States → concepts (initial gets the replacement; others fresh).
            let mut states_to_concepts: HashMap<usize, ClassExpr> = HashMap::new();
            for state in automaton.states() {
                if automaton.is_initial(state) {
                    states_to_concepts.insert(state, replacement_value.clone());
                } else {
                    let mut state_concept = self.fresh_class(first_replacement_index);
                    first_replacement_index += 1;
                    if is_of_negative_polarity {
                        state_concept = self.complement(&state_concept);
                    }
                    states_to_concepts.insert(state, state_concept);
                }
            }
            // Transitions.
            for transition in automaton.delta() {
                let from_state_concept = self.complement(&states_to_concepts[&transition.start]);
                let to_state_concept = states_to_concepts[&transition.end].clone();
                match transition.label {
                    None => {
                        axioms
                            .concept_inclusions
                            .push(vec![from_state_concept, to_state_concept]);
                    }
                    Some(label) => {
                        let consequent_all = CE::ObjectAllValuesFrom {
                            ope: label,
                            bce: Box::new(to_state_concept),
                        };
                        axioms
                            .concept_inclusions
                            .push(vec![from_state_concept, consequent_all]);
                    }
                }
            }
            // Final states.
            for final_state in automaton.terminals() {
                let final_complement = self.complement(&states_to_concepts[&final_state]);
                if is_owl_nothing(&filler) {
                    axioms.concept_inclusions.push(vec![final_complement]);
                } else {
                    axioms
                        .concept_inclusions
                        .push(vec![final_complement, filler.clone()]);
                }
            }
        }
        Ok(())
    }
}

fn is_owl_thing(ce: &ClassExpr) -> bool {
    matches!(ce, CE::Class(c) if c.0.to_string() == OWL_THING)
}

fn is_owl_nothing(ce: &ClassExpr) -> bool {
    matches!(ce, CE::Class(c) if c.0.to_string() == OWL_NOTHING)
}

// ---------------------------------------------------------------------------
// Automaton construction (forward fragment).
// ---------------------------------------------------------------------------

fn create_automata(
    automata_by_property: &mut HashMap<ObjectPropExpr, Automaton>,
    axioms: &mut OWLAxioms,
) -> Result<(), String> {
    let simple: Vec<[ObjectPropExpr; 2]> = axioms.simple_object_property_inclusions.clone();
    // Faithful port of Java `createAutomata`/`buildIndividualAutomata`: the raw
    // `complexObjectPropertyInclusions` are passed straight through and the
    // automaton is keyed on `superObjectProperty` EVEN WHEN it is anonymous
    // (`Inv(r)`). `buildPropertyOrdering` adds edges to the anonymous super and
    // the mirror-fill / inverse passes derive the named `r`. (Previously the
    // Rust normalized an inverse super up front, S1∘...∘Sn ⊑ Inv(r) ⇒
    // Inv(Sn)∘...∘Inv(S1) ⊑ r, keying on the named `r`; that diverged from Java.)
    let complex: Vec<(Vec<ObjectPropExpr>, ObjectPropExpr)> = axioms
        .complex_object_property_inclusions
        .iter()
        .map(|c| {
            (
                c.sub_object_properties.clone(),
                c.super_object_property.clone(),
            )
        })
        .collect();

    // The full role-box automaton machinery is ported: the forward chain
    // fragment, plus the inverse/symmetric/equivalent extensions HermiT threads
    // through `connectAllAutomata` / `finalizeConstruction`. Equivalent
    // properties share automata; inverse sub/super-properties are handled by the
    // mirror substitution / normalization; the symmetric splice and the
    // transitive-inverse loop are applied in `finalize_construction`; and the
    // inverse-union passes enrich a property's automaton with the (mirror of)
    // its complex inverse's automaton.
    let equivalent = find_equivalent_properties(&simple);

    let property_dependency_graph = build_property_ordering(&simple, &complex, &equivalent)?;
    check_for_regularity(&property_dependency_graph, &equivalent)?;

    let mut complex_dependency_graph = property_dependency_graph.clone();
    let mut transitive_properties: HashSet<ObjectPropExpr> = HashSet::new();
    let mut individual_automata = build_individual_automata(
        &mut complex_dependency_graph,
        &complex,
        &equivalent,
        &mut transitive_properties,
    )?;

    // Properties that are both symmetric (`r ⊑ Inv(r)` / `Inv(r) ⊑ r`)
    // and complex need the symmetric language spliced into their automaton in
    // `finalize_construction` (Java `findSymmetricProperties`, threaded into
    // `finalizeConstruction`).
    let symmetric_properties = find_symmetric_properties(&simple);
    let inverse_map = build_inverse_properties_map(&simple);

    let simple_properties = find_simple_properties(&complex_dependency_graph, &individual_automata);

    let mut property_dependency_graph = property_dependency_graph;
    property_dependency_graph.remove_elements(&simple_properties);
    complex_dependency_graph.remove_elements(&simple_properties);

    for element in complex_dependency_graph.get_elements().clone() {
        axioms.complex_object_property_expressions.insert(element);
    }

    // A simple sub-property of a complex property contributes a direct
    // transition into that property's automaton.
    for inclusion in &simple {
        if axioms.complex_object_property_expressions.contains(&inclusion[0])
            && individual_automata.contains_key(&inclusion[1])
        {
            let automaton = individual_automata.get_mut(&inclusion[1]).unwrap();
            let initial = automaton.initial_state();
            let final_state = automaton.final_state();
            automaton.add_transition(initial, Some(inclusion[0].clone()), final_state);
        }
    }

    let inverse_of_complex: Vec<ObjectPropExpr> = axioms
        .complex_object_property_expressions
        .iter()
        .map(inverse_property)
        .collect();
    for property in inverse_of_complex {
        axioms.complex_object_property_expressions.insert(property);
    }

    connect_all_automata(
        automata_by_property,
        &property_dependency_graph,
        &individual_automata,
        &inverse_map,
        &symmetric_properties,
        &transitive_properties,
    );

    // `∀Inv(R).C` support: the automaton of an inverse property is the mirror
    // of the property's automaton (HermiT's `finalizeConstruction`).
    // Java runs the mirror-fill twice (ObjectPropertyInclusionManager.java
    // :342-347 then 350-354), with a `putAll` of the staged mirrors into the live
    // map BETWEEN the two passes, so the second pass observes inverses added by
    // the first pass (mirrors of mirrors). Both passes use the same effective
    // guard (line 351's first conjunct is always true while iterating the map):
    // for each entry whose inverse has no automaton, stage `getMirroredCopy`.
    for _ in 0..2 {
        let mut existing: Vec<(ObjectPropExpr, Automaton)> = automata_by_property
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let n_existing = existing.len();
        existing.sort_by_key(|(k, _)| java_map_order_key(k, n_existing));
        let mut extra_inverse: HashMap<ObjectPropExpr, Automaton> = HashMap::new();
        for (property, automaton) in existing {
            let inverse = inverse_property(&property);
            if !automata_by_property.contains_key(&inverse) {
                extra_inverse.insert(inverse, mirrored_copy(&automaton));
            }
        }
        automata_by_property.extend(extra_inverse);
    }

    // Port of `connectAllAutomata`'s final `inversePropertiesMap` pass: for every
    // property with a *declared* inverse (an `InverseObjectProperties`/`r ⊑ Inv(s)`
    // relationship), enrich the property's automaton with the (mirrored) automaton
    // of its inverse, so `∀property.C` propagates along the inverse's reversed
    // regular language. Without this, `∀r.C` over `InverseObjectProperties(r, s)`
    // with a *complex* `s` (transitive / chain super-role) under-propagates.
    // Java order: this pass runs INSIDE connectAllAutomata (line ~357) BEFORE the
    // equivalent-role clone block (line ~207), so equivalent-role cloning sees the
    // inverse-enriched automata (ObjectPropertyInclusionManager.java:357-372,207-228).
    if !inverse_map.is_empty() {
        // Java iterates the LIVE `completeAutomata` (ObjectPropertyInclusionManager
        // .java:357-372). `autoOfPropExpr = entry.getValue()` is the live map's
        // value; `increaseAutomatonWithInversePropertyAutomaton` mutates it in
        // place, so the inverse automaton read by later iterations
        // (`completeAutomata.get(inverseProp)`) observes enrichment accumulated by
        // earlier iterations. The else-branch mirrors are staged with `put`
        // (overwrite) and only merged into the live map at the closing `putAll`, so
        // they are not visible to the in-loop live-map reads.
        let mut keys: Vec<ObjectPropExpr> = automata_by_property.keys().cloned().collect();
        let n_keys = keys.len();
        keys.sort_by_key(|k| java_map_order_key(k, n_keys));
        let mut extra: HashMap<ObjectPropExpr, Automaton> = HashMap::new();
        for property in keys {
            let Some(inverses) = inverse_map.get(&property) else { continue };
            let mut inverses: Vec<&ObjectPropExpr> = inverses.iter().collect();
            let n_inv = inverses.len();
            inverses.sort_by_key(|p| java_map_order_key(p, n_inv));
            for inverse_prop in inverses {
                if let Some(inverse_automaton) = automata_by_property.get(inverse_prop).cloned() {
                    // Java line 363-364: enrich the live entry in place.
                    let automaton = automata_by_property.get_mut(&property).unwrap();
                    increase_automaton_with_inverse(automaton, &inverse_automaton);
                } else {
                    let mirrored = mirrored_copy(&automata_by_property[&property]);
                    extra.insert(inverse_prop.clone(), mirrored);
                }
            }
        }
        automata_by_property.extend(extra);
    }

    // Equivalent properties share an automaton: each equivalent of a property
    // with an automaton gets a clone of it (and its inverse the mirror), porting
    // `individualAutomataForEquivRoles`. Runs AFTER the inverse-map pass so that
    // cloning sees inverse-enriched automata (Java: line ~207-228 after connectAllAutomata).
    let mut snapshot: Vec<(ObjectPropExpr, Automaton)> = automata_by_property
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let n_snap = snapshot.len();
    snapshot.sort_by_key(|(k, _)| java_map_order_key(k, n_snap));
    let mut equivalent_automata: HashMap<ObjectPropExpr, Automaton> = HashMap::new();
    for (property, automaton) in snapshot {
        if let Some(equiv_set) = equivalent.get(&property) {
            let mut equiv_set: Vec<&ObjectPropExpr> = equiv_set.iter().collect();
            let n_eq = equiv_set.len();
            equiv_set.sort_by_key(|p| java_map_order_key(p, n_eq));
            for equiv_property in equiv_set {
                if *equiv_property != property
                    && !automata_by_property.contains_key(equiv_property)
                {
                    equivalent_automata.insert(equiv_property.clone(), automaton.clone());
                    axioms
                        .complex_object_property_expressions
                        .insert(equiv_property.clone());
                }
                let inverse_equiv = inverse_property(equiv_property);
                if inverse_equiv != property
                    && !automata_by_property.contains_key(&inverse_equiv)
                {
                    equivalent_automata.insert(inverse_equiv.clone(), mirrored_copy(&automaton));
                    axioms
                        .complex_object_property_expressions
                        .insert(inverse_equiv);
                }
            }
        }
    }
    // Merge the equivalent-role clones into the automata map (Java
    // `automataByProperty.putAll(individualAutomataForEquivRoles)`, line ~228).
    // Without this the clones built above are discarded, so a property equivalent
    // to a complex one (e.g. `s` with `r ≡ s`, `r` transitive) gets no automaton
    // and `∀s.C` fails to propagate along its (shared) chains.
    automata_by_property.extend(equivalent_automata);
    Ok(())
}

/// Port of `findEquivalentProperties`: groups mutually-included properties.
/// Drives the dependency-graph construction, the chain-label substitution, the
/// equivalent-property regularity trimming, and the shared-automaton cloning.
fn find_equivalent_properties(
    simple: &[[ObjectPropExpr; 2]],
) -> HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>> {
    let mut graph: Graph<ObjectPropExpr> = Graph::new();
    for inclusion in simple {
        if inclusion[0] != inclusion[1] && inclusion[0] != inverse_property(&inclusion[1]) {
            graph.add_edge(inclusion[0].clone(), inclusion[1].clone());
        }
    }
    graph.transitively_close();
    let mut result: HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>> = HashMap::new();
    for obj in graph.get_elements().clone() {
        let successors = graph.get_successors(&obj);
        let inv = inverse_property(&obj);
        if successors.contains(&obj) || successors.contains(&inv) {
            let mut equiv: HashSet<ObjectPropExpr> = HashSet::new();
            for succ in &successors {
                if *succ != obj {
                    let succ_succ = graph.get_successors(succ);
                    if succ_succ.contains(&obj) || succ_succ.contains(&inv) {
                        equiv.insert(succ.clone());
                    }
                }
            }
            result.insert(obj, equiv);
        }
    }
    result
}

/// Port of `findSymmetricProperties` (~lines 230-238): a property is symmetric
/// when it appears in an inclusion `R ⊑ Inv(R)` (equivalently `Inv(R) ⊑ R`).
/// Both `R` and `Inv(R)` are recorded so the symmetric splice is applied to
/// either orientation in `finalize_construction`.
fn find_symmetric_properties(simple: &[[ObjectPropExpr; 2]]) -> HashSet<ObjectPropExpr> {
    let mut result: HashSet<ObjectPropExpr> = HashSet::new();
    for inclusion in simple {
        if inverse_property(&inclusion[1]) == inclusion[0]
            || inclusion[1] == inverse_property(&inclusion[0])
        {
            result.insert(inclusion[0].clone());
            result.insert(inverse_property(&inclusion[0]));
        }
    }
    result
}

/// Port of `buildInversePropertiesMap` (~lines 239-270): maps each property to
/// the set of properties declared as its inverse via an inclusion whose other
/// side is an `Inv(...)` expression (`InverseObjectProperties`, `R ⊑ Inv(S)`).
fn build_inverse_properties_map(
    simple: &[[ObjectPropExpr; 2]],
) -> HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>> {
    let mut map: HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>> = HashMap::new();
    for inclusion in simple {
        if is_anonymous_property(&inclusion[1]) {
            map.entry(inclusion[0].clone())
                .or_default()
                .insert(inverse_property(&inclusion[1]));
            map.entry(inverse_property(&inclusion[1]))
                .or_default()
                .insert(inclusion[0].clone());
        } else if is_anonymous_property(&inclusion[0]) {
            map.entry(inclusion[1].clone())
                .or_default()
                .insert(inverse_property(&inclusion[0]));
            map.entry(inverse_property(&inclusion[0]))
                .or_default()
                .insert(inclusion[1].clone());
        }
    }
    map
}

/// Port of `buildPropertyOrdering`: the sub→super dependency graph, raising the
/// regularity error for the irregular structural cases it detects.
fn build_property_ordering(
    simple: &[[ObjectPropExpr; 2]],
    complex: &[(Vec<ObjectPropExpr>, ObjectPropExpr)],
    equivalent: &HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>>,
) -> Result<Graph<ObjectPropExpr>, String> {
    let mut graph: Graph<ObjectPropExpr> = Graph::new();
    for inclusion in simple {
        // No edge between equivalent properties (else the dependency graph would
        // be cyclic and fail the regularity check).
        let are_equivalent = equivalent
            .get(&inclusion[0])
            .is_some_and(|s| s.contains(&inclusion[1]));
        if inclusion[0] != inclusion[1]
            && inclusion[0] != inverse_property(&inclusion[1])
            && !are_equivalent
        {
            graph.add_edge(inclusion[0].clone(), inclusion[1].clone());
        }
    }
    let not_regular = || "The given property hierarchy is not regular.".to_string();
    for (subs, sup) in complex {
        let n = subs.len();
        if n != 2 && *sup == subs[0] && *sup == subs[n - 1] {
            return Err(not_regular());
        }
        for (i, sub) in subs.iter().enumerate() {
            // Java rejects a middle role that equals the super-role OR is
            // equivalent to it (via the equivalent-properties closure).
            let sub_equiv_sup = equivalent.get(sup).is_some_and(|s| s.contains(sub));
            if n != 2 && i > 0 && i < n - 1 && (sub == sup || sub_equiv_sup) {
                return Err(not_regular());
            } else if inverse_property(sub) == *sup {
                return Err(not_regular());
            } else if sub != sup {
                graph.add_edge(sub.clone(), sup.clone());
            }
        }
    }
    Ok(graph)
}

/// Port of `checkForRegularity` (~lines 631-660), including the equivalent-
/// property trimming loop. Before transitively closing and looking for a cycle,
/// HermiT iteratively REMOVES every edge `prop -> succProp` whose endpoints are
/// equivalent properties, reconnecting `prop` to `succProp`'s successors. This
/// prevents a benign `a -> b -> a` cycle between equivalent properties (e.g.
/// `a≡b` with cross-chains `a∘x⊑b`, `b∘y⊑a`) from being misreported as an
/// irregular hierarchy.
fn check_for_regularity(
    property_dependency_graph: &Graph<ObjectPropExpr>,
    equivalent: &HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>>,
) -> Result<(), String> {
    let mut graph = property_dependency_graph.clone();

    // do/while trimming loop (Java `do { ... } while (trimmed);`).
    let mut trimmed = true;
    while trimmed {
        trimmed = false;
        // Iterate over a clone so the live graph can be mutated in place.
        let temp = graph.clone();
        for prop in temp.get_elements().clone() {
            for succ_prop in temp.get_successors(&prop) {
                let prop_equiv_succ = equivalent
                    .get(&prop)
                    .is_some_and(|s| s.contains(&succ_prop));
                if prop_equiv_succ {
                    for succ_prop_succ in temp.get_successors(&succ_prop) {
                        if prop != succ_prop_succ {
                            graph.add_edge(prop.clone(), succ_prop_succ);
                        }
                    }
                    trimmed = true;
                    graph.remove_edge(&prop, &succ_prop);
                }
            }
        }
    }

    graph.transitively_close();
    for prop in graph.get_elements().clone() {
        let successors = graph.get_successors(&prop);
        if successors.contains(&prop) || successors.contains(&inverse_property(&prop)) {
            return Err(format!(
                "The given property hierarchy is not regular. Cyclic dependency involving {:?}",
                prop
            ));
        }
    }
    Ok(())
}

/// Port of `buildIndividualAutomata`: the per-super-property automaton built
/// directly from its complex inclusions (the four chain shapes).
fn build_individual_automata(
    complex_dependency_graph: &mut Graph<ObjectPropExpr>,
    complex: &[(Vec<ObjectPropExpr>, ObjectPropExpr)],
    equivalent: &HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>>,
    transitive_properties: &mut HashSet<ObjectPropExpr>,
) -> Result<HashMap<ObjectPropExpr, Automaton>, String> {
    // Java rewrites every chain transition label to the super-property when the
    // label is equivalent to it (`if (equivalentPropertiesMap.containsKey(...)
    // && ...contains(transitionLabel)) transitionLabel=superObjectProperty;`).
    let substitute_label = |sup: &ObjectPropExpr, label: &ObjectPropExpr| -> ObjectPropExpr {
        if equivalent.get(sup).is_some_and(|s| s.contains(label)) {
            sup.clone()
        } else {
            label.clone()
        }
    };
    let mut automata_map: HashMap<ObjectPropExpr, Automaton> = HashMap::new();
    for (subs, sup) in complex {
        let (initial_state, final_state) = if !automata_map.contains_key(sup) {
            let mut automaton = Automaton::new();
            let initial = automaton.add_state(true, false);
            let finalst = automaton.add_state(false, true);
            automaton.add_transition(initial, Some(sup.clone()), finalst);
            automata_map.insert(sup.clone(), automaton);
            (initial, finalst)
        } else {
            let automaton = &automata_map[sup];
            (automaton.initial_state(), automaton.final_state())
        };
        let n = subs.len();
        let automaton = automata_map.get_mut(sup).unwrap();
        if n == 2 && subs[0] == *sup && subs[1] == *sup {
            // R R -> R : transitivity (an ε loop final → initial).
            automaton.add_transition(final_state, None, initial_state);
            transitive_properties.insert(sup.clone());
        } else if subs[0] == *sup {
            // R S2 ... Sn -> R
            let mut from_state = final_state;
            for sub in subs.iter().take(n - 1).skip(1) {
                from_state = automaton.add_new_transition(from_state, substitute_label(sup, sub));
            }
            automaton.add_transition(
                from_state,
                Some(substitute_label(sup, &subs[n - 1])),
                final_state,
            );
        } else if subs[n - 1] == *sup {
            // S1 ... Sn-1 R -> R
            let mut from_state = initial_state;
            for sub in subs.iter().take(n - 2) {
                from_state = automaton.add_new_transition(from_state, substitute_label(sup, sub));
            }
            automaton.add_transition(
                from_state,
                Some(substitute_label(sup, &subs[n - 2])),
                initial_state,
            );
        } else {
            // S1 ... Sn -> R
            let mut from_state = initial_state;
            for sub in subs.iter().take(n - 1) {
                from_state = automaton.add_new_transition(from_state, substitute_label(sup, sub));
            }
            automaton.add_transition(
                from_state,
                Some(substitute_label(sup, &subs[n - 1])),
                final_state,
            );
        }
    }
    // A purely transitive super-property has no dependency edges; register it as
    // a self-dependent complex property so it is not classified as simple.
    for (subs, sup) in complex {
        if subs.len() == 2 && subs[0] == *sup && subs[1] == *sup {
            let inverse = inverse_property(sup);
            if !complex_dependency_graph.get_elements().contains(sup)
                && !automata_map.contains_key(&inverse)
            {
                complex_dependency_graph.add_edge(sup.clone(), sup.clone());
                let mirrored = mirrored_copy(&automata_map[sup]);
                automata_map.insert(inverse, mirrored);
            }
        }
    }
    // Java always constructs an automaton for owl:topObjectProperty since it
    // might occur in queries (the axiomatisation at query time fails otherwise):
    // an initial -> final transition on the top role plus an ε self-loop
    // (transitivity). See buildIndividualAutomata ~lines 784-800.
    let top = top_object_property();
    if !automata_map.contains_key(&top) {
        let mut automaton = Automaton::new();
        let initial = automaton.add_state(true, false);
        let finalst = automaton.add_state(false, true);
        automaton.add_transition(initial, Some(top.clone()), finalst);
        automaton.add_transition(finalst, None, initial); // transitivity
        automata_map.insert(top, automaton);
    }
    Ok(automata_map)
}

/// The `owl:topObjectProperty` expression (Java's
/// `df.getOWLTopObjectProperty()`).
fn top_object_property() -> ObjectPropExpr {
    let build: Build<super::A> = Build::new_arc();
    ObjectPropExpr::ObjectProperty(
        build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty"),
    )
}

/// Port of `findSimpleProperties`.
fn find_simple_properties(
    complex_dependency_graph: &Graph<ObjectPropExpr>,
    individual_automata: &HashMap<ObjectPropExpr, Automaton>,
) -> HashSet<ObjectPropExpr> {
    let mut simple_properties: HashSet<ObjectPropExpr> = HashSet::new();

    let mut with_inverses = complex_dependency_graph.clone();
    for property1 in complex_dependency_graph.get_elements().clone() {
        for property2 in complex_dependency_graph.get_successors(&property1) {
            with_inverses.add_edge(inverse_property(&property1), inverse_property(&property2));
        }
    }

    let mut inverted = with_inverses.get_inverse();
    inverted.transitively_close();

    for property in inverted.get_elements().clone() {
        let mut has_complex_subproperty = false;
        for sub in inverted.get_successors(&property) {
            if individual_automata.contains_key(&sub)
                || individual_automata.contains_key(&inverse_property(&sub))
            {
                has_complex_subproperty = true;
                break;
            }
        }
        if !has_complex_subproperty
            && !individual_automata.contains_key(&property)
            && !individual_automata.contains_key(&inverse_property(&property))
        {
            simple_properties.insert(property);
        }
    }
    simple_properties
}

/// Port of `increaseWithDefinedInverseIfNecessary` (Java 541-556): if the
/// property has a declared inverse in `inversePropertiesMap` with its own
/// individual automaton, splice that inverse's individual automaton into this
/// property's automaton before `finalizeConstruction`.
fn increase_with_defined_inverse_if_necessary(
    property: &ObjectPropExpr,
    automaton: &mut Automaton,
    inverse_map: &HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>>,
    individual_automata: &HashMap<ObjectPropExpr, Automaton>,
) {
    if let Some(inverses) = inverse_map.get(property) {
        for inverse in inverses {
            if individual_automata.contains_key(inverse) && inverse != property {
                // Java 548: splice the inverse's INDIVIDUAL automaton.
                let inv_auto = individual_automata[inverse].clone();
                increase_automaton_with_inverse(automaton, &inv_auto);
            }
        }
    } else {
        // Java 552-555: else-if Inv(R) (anonymous) has an individual automaton.
        let inv_prop = inverse_property(property);
        if individual_automata.contains_key(&inv_prop) {
            let inv_auto = individual_automata[&inv_prop].clone();
            increase_automaton_with_inverse(automaton, &inv_auto);
        }
    }
}

fn increase_automaton_with_inverse(property_automaton: &mut Automaton, inverse_automaton: &Automaton) {
    let initial = property_automaton.initial_state();
    let finalst = property_automaton.final_state();
    let mirrored = mirrored_copy(inverse_automaton);
    automata_connector(property_automaton, &mirrored, initial, finalst);
}

/// Port of `connectAllAutomata`: builds each property's complete automaton by
/// substituting its sub-properties' automata, then finalizes each (transitive-
/// inverse ε-loop + symmetric splice). The `inverse_dependency_graph` /
/// `symmetric_properties` / `transitive_properties` are threaded through so
/// `finalize_construction` (Java's `finalizeConstruction`) can be applied at the
/// point each automaton is completed.
fn connect_all_automata(
    complete_automata: &mut HashMap<ObjectPropExpr, Automaton>,
    property_dependency_graph: &Graph<ObjectPropExpr>,
    individual_automata: &HashMap<ObjectPropExpr, Automaton>,
    inverse_map: &HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>>,
    symmetric_properties: &HashSet<ObjectPropExpr>,
    transitive_properties: &HashSet<ObjectPropExpr>,
) {
    let mut trans_closed = property_dependency_graph.clone();
    trans_closed.transitively_close();

    let mut properties_to_start: Vec<ObjectPropExpr> = Vec::new();
    for prop in trans_closed.get_elements() {
        if trans_closed.successors_is_empty(prop) {
            properties_to_start.push(prop.clone());
        }
    }
    // Java seeds the recursion with the SINKS of the transitively-closed
    // dependency graph only (`propertiesToStartRecursion`), and everything else is
    // reached by the descent from them. Seeding every element instead changes which
    // automaton a property is built from and over-enriches: EFO's transitive
    // `has_disease_location` then subsumed classes Java leaves alone. Gated behind
    // the env var while the faithful behaviour is verified.
    // Iterate in a fixed order (see `prop_sort_key`): the recursion start order is
    // not answer-neutral, so a stable order reproduces Java's deterministic result.
    let n_pts = properties_to_start.len();
    properties_to_start.sort_by_key(|p| java_map_order_key(p, n_pts));
    // HermiT iterates `propertiesToStartRecursion` as a `HashSet`. Java's hashing
    // is content-based and so stable across runs; our `std::HashSet` randomises its
    // iteration order per run. The order is NOT answer-neutral here: building a
    // property `R` finalises (and caches the mirror of) `Inv(R)`, so processing
    // `Inv(R)` before any super-property `S ⊒ R` (whose recursion descends into `R`)
    // means that descent hits the cached, correctly-built automaton for `R` instead
    // of re-building it directly and wrongly embedding `R`'s complex sub-property
    // chains (which would make `∀S.C` over-propagate — an order-dependent
    // unsoundness). A fixed order reproduces Java's stable, sound behaviour.
    // successors in this graph = sub-properties.
    let inverse_dependency_graph = property_dependency_graph.get_inverse();

    // Tracks the properties currently on the recursion stack, so a cyclic
    // complex-property dependency is broken instead of recursing forever (see the
    // guard in `build_complete_automaton`). Balanced insert/remove keeps it empty
    // between top-level seeds.
    let mut building: HashSet<ObjectPropExpr> = HashSet::new();
    for superproperty in properties_to_start {
        build_complete_automaton(
            &superproperty,
            individual_automata,
            complete_automata,
            &inverse_dependency_graph,
            inverse_map,
            symmetric_properties,
            transitive_properties,
            &mut building,
        );
    }

    // Port of `connectAllAutomata`'s leftover-individual-automata loop
    // (~lines 329-341). For each property with an individual automaton lacking a
    // complete automaton, if its inverse has an automaton (in `complete_automata`,
    // where the inverse is in the dependency graph, or in `individual_automata`),
    // enrich the property's automaton with the (mirror of the) inverse's
    // automaton before storing it, so `∀property.C` propagates along the
    // inverse of a complex role even when the property is only a leftover leaf.
    let mut individual_keys: Vec<&ObjectPropExpr> = individual_automata.keys().collect();
    let n_ik = individual_keys.len();
    individual_keys.sort_by_key(|p| java_map_order_key(p, n_ik));
    for property in individual_keys {
        let automaton = &individual_automata[property];
        if complete_automata.contains_key(property) {
            continue;
        }
        let inverse = inverse_property(property);
        let inverse_in_graph = inverse_dependency_graph.get_elements().contains(&inverse);
        let mut property_automaton = automaton.clone();
        // Java gates on `(complete.has(inv) && invGraph.contains(inv)) ||
        // individual.has(inv)`, then ALWAYS prefers `complete.get(inv)`,
        // falling back to `individual.get(inv)` only when the complete
        // automaton is absent.
        if (complete_automata.contains_key(&inverse) && inverse_in_graph)
            || individual_automata.contains_key(&inverse)
        {
            let inverse_automaton = complete_automata
                .get(&inverse)
                .or_else(|| individual_automata.get(&inverse))
                .cloned();
            if let Some(inverse_automaton) = inverse_automaton {
                increase_automaton_with_inverse(&mut property_automaton, &inverse_automaton);
            }
        }
        // Java line 339: bare put — no transitive-ε loop, no symmetric splice, no
        // inverse mirror; those are applied by `finalize_construction` and the
        // inverse-map / equivalent-role passes that follow.
        complete_automata.insert(property.clone(), property_automaton);
    }
}

/// Port of `finalizeConstruction` (~lines 524-540). Applies the two language
/// extensions HermiT adds once a property's automaton is otherwise complete and
/// stores the automaton (and the mirror for its inverse):
///   * if `Inv(R)` is transitive, an ε transition `terminal -> initial`
///     (so `∀R.C` keeps propagating around the transitive loop);
///   * if `R` is symmetric, splice `getMirroredCopy(automaton)` along an
///     `Inv(R)`-labelled basic transition, so the symmetric (reversed)
///     language is recognised even for a *non-simple* `R`.
fn finalize_construction(
    complete_automata: &mut HashMap<ObjectPropExpr, Automaton>,
    property: &ObjectPropExpr,
    mut automaton: Automaton,
    symmetric_properties: &HashSet<ObjectPropExpr>,
    transitive_properties: &HashSet<ObjectPropExpr>,
) {
    if transitive_properties.contains(&inverse_property(property)) {
        let terminal = automaton.final_state();
        let initial = automaton.initial_state();
        automaton.add_transition(terminal, None, initial);
    }
    if symmetric_properties.contains(property) {
        // The basic `Inv(R)`-labelled transition the mirror is spliced into runs
        // from the automaton's initial to its terminal state (Java
        // `new Transition(initials, Inv(R), terminals)`).
        let initial = automaton.initial_state();
        let terminal = automaton.final_state();
        let mirrored = mirrored_copy(&automaton);
        automata_connector(&mut automaton, &mirrored, initial, terminal);
    }
    complete_automata.insert(property.clone(), automaton.clone());
    // Java stores the authoritative mirror for the inverse unconditionally
    // (`completeAutomata.put(prop.getInverseProperty(), getMirroredCopy(auto))`),
    // replacing any entry an earlier mutually-recursive step left behind.
    complete_automata.insert(inverse_property(property), mirrored_copy(&automaton));
}

/// Port of `buildCompleteAutomataForProperties` (forward fragment), finalizing
/// each completed automaton via `finalize_construction`. Wrapper: the memo check
/// plus a cycle guard on `building` (the set of properties currently on the build
/// stack). Because the seeding above starts the recursion from EVERY property (not
/// just Java's sinks, for forward-chain completeness), a cyclic complex-property
/// dependency — e.g. equivalent properties with cross-chains (`a≡b`, `a∘x⊑b`,
/// `b∘y⊑a`) give `a→b→a` — would otherwise recurse forever. Java never enters such
/// a cycle. On re-entry of a property still being built, return its own
/// (individual, else single-transition) language to break the loop; the outer
/// build still completes and stores the full automaton. Acyclic hierarchies
/// (including EFO) never re-enter, so this is behaviour-preserving for them.
#[allow(clippy::too_many_arguments)]
fn build_complete_automaton(
    property: &ObjectPropExpr,
    individual_automata: &HashMap<ObjectPropExpr, Automaton>,
    complete_automata: &mut HashMap<ObjectPropExpr, Automaton>,
    inverse_dependency_graph: &Graph<ObjectPropExpr>,
    inverse_map: &HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>>,
    symmetric_properties: &HashSet<ObjectPropExpr>,
    transitive_properties: &HashSet<ObjectPropExpr>,
    building: &mut HashSet<ObjectPropExpr>,
) -> Automaton {
    if let Some(automaton) = complete_automata.get(property) {
        return automaton.clone();
    }
    if building.contains(property) {
        return individual_automata.get(property).cloned().unwrap_or_else(|| {
            let mut automaton = Automaton::new();
            let initial = automaton.add_state(true, false);
            let finalst = automaton.add_state(false, true);
            automaton.add_transition(initial, Some(property.clone()), finalst);
            automaton
        });
    }
    building.insert(property.clone());
    let result = build_complete_automaton_inner(
        property,
        individual_automata,
        complete_automata,
        inverse_dependency_graph,
        inverse_map,
        symmetric_properties,
        transitive_properties,
        building,
    );
    building.remove(property);
    result
}

#[allow(clippy::too_many_arguments)]
fn build_complete_automaton_inner(
    property: &ObjectPropExpr,
    individual_automata: &HashMap<ObjectPropExpr, Automaton>,
    complete_automata: &mut HashMap<ObjectPropExpr, Automaton>,
    inverse_dependency_graph: &Graph<ObjectPropExpr>,
    inverse_map: &HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>>,
    symmetric_properties: &HashSet<ObjectPropExpr>,
    transitive_properties: &HashSet<ObjectPropExpr>,
    building: &mut HashSet<ObjectPropExpr>,
) -> Automaton {
    // Java 384-388: for ANY property (named or anonymous) whose inverse already
    // has a COMPLETE automaton and which has no individual automaton, the complete
    // automaton is the mirror of the inverse's complete automaton. Gated only by
    // `completeAutomata.containsKey(Inv(R)) && !individualAutomata.containsKey(R)`.
    if complete_automata.contains_key(&inverse_property(property))
        && !individual_automata.contains_key(property)
    {
        let mirrored = mirrored_copy(&complete_automata[&inverse_property(property)]);
        complete_automata.insert(property.clone(), mirrored.clone());
        return mirrored;
    }

    // Java 390: a property is a "leaf" only when neither it nor its inverse has
    // any complex sub-property in the dependency graph.
    let sub_properties = inverse_dependency_graph.get_successors(property);
    let inverse_sub_properties = inverse_dependency_graph.get_successors(&inverse_property(property));

    if sub_properties.is_empty() && inverse_sub_properties.is_empty() {
        // Leaf property.
        if let Some(own) = individual_automata.get(property).cloned() {
            // Java 432-446: has its own automaton; enrich with the inverse's
            // language and finalize.
            return apply_inverse_and_finalize(
                property,
                own,
                individual_automata,
                complete_automata,
                inverse_dependency_graph,
                inverse_map,
                symmetric_properties,
                transitive_properties,
                true,
                building,
            );
        }
        // Java 393-417: no own automaton. If a declared inverse has its own
        // automaton, the leaf automaton is the mirror of that inverse's COMPLETE
        // automaton (stored directly, without finalization).
        if let Some(inverses) = inverse_map.get(property) {
            for inverse in inverses {
                if individual_automata.contains_key(inverse) && inverse != property {
                    let inv_complete = build_complete_automaton(
                        inverse,
                        individual_automata,
                        complete_automata,
                        inverse_dependency_graph,
                        inverse_map,
                        symmetric_properties,
                        transitive_properties,
                        building,
                    );
                    let mirrored = mirrored_copy(&inv_complete);
                    complete_automata.insert(property.clone(), mirrored.clone());
                    return mirrored;
                }
            }
        } else if individual_automata.contains_key(&inverse_property(property)) {
            // Java 407-417: else-if Inv(R) has an automaton.
            let inv_prop = inverse_property(property);
            let inv_complete = build_complete_automaton(
                &inv_prop,
                individual_automata,
                complete_automata,
                inverse_dependency_graph,
                inverse_map,
                symmetric_properties,
                transitive_properties,
                building,
            );
            if complete_automata.contains_key(property) {
                return complete_automata[property].clone();
            }
            let mirrored = mirrored_copy(&inv_complete);
            complete_automata.insert(property.clone(), mirrored.clone());
            return mirrored;
        }
        // Java 418-430: no inverse with an automaton; a single-transition
        // automaton, finalized.
        let mut automaton = Automaton::new();
        let initial = automaton.add_state(true, false);
        let finalst = automaton.add_state(false, true);
        automaton.add_transition(initial, Some(property.clone()), finalst);
        finalize_construction(
            complete_automata,
            property,
            automaton,
            symmetric_properties,
            transitive_properties,
        );
        return complete_automata[property].clone();
    }

    // Non-leaf property.
    let has_own_automaton = individual_automata.contains_key(property);
    let bigger = if let Some(bigger) = individual_automata.get(property).cloned() {
        // The property has its own automaton; substitute sub-property automata
        // into every transition labelled by a (complex) sub-property.
        let mut bigger = bigger;
        for smaller_property in &sub_properties {
            let mut matched = false;
            for transition in bigger.delta() {
                if transition.label.as_ref() == Some(smaller_property) {
                    let smaller = build_complete_automaton(
                        smaller_property,
                        individual_automata,
                        complete_automata,
                        inverse_dependency_graph,
                        inverse_map,
                        symmetric_properties,
                        transitive_properties,
                        building,
                    );
                    if smaller.delta().len() != 1 {
                        automata_connector(
                            &mut bigger,
                            &smaller,
                            transition.start,
                            transition.end,
                        );
                    }
                    matched = true;
                }
            }
            if !matched {
                let smaller = build_complete_automaton(
                    smaller_property,
                    individual_automata,
                    complete_automata,
                    inverse_dependency_graph,
                    inverse_map,
                    symmetric_properties,
                    transitive_properties,
                    building,
                );
                let initial = bigger.initial_state();
                let finalst = bigger.final_state();
                automata_connector(&mut bigger, &smaller, initial, finalst);
            }
        }
        bigger
    } else {
        // No own automaton: a fresh initial→final transition, with each
        // sub-property's automaton spliced in (and a direct sub-property edge).
        let mut bigger = Automaton::new();
        let initial = bigger.add_state(true, false);
        let finalst = bigger.add_state(false, true);
        bigger.add_transition(initial, Some(property.clone()), finalst);
        for smaller_property in &sub_properties {
            let smaller = build_complete_automaton(
                smaller_property,
                individual_automata,
                complete_automata,
                inverse_dependency_graph,
                inverse_map,
                symmetric_properties,
                transitive_properties,
                building,
            );
            automata_connector(&mut bigger, &smaller, initial, finalst);
            bigger.add_transition(initial, Some(smaller_property.clone()), finalst);
        }
        bigger
    };

    // Java applies the inverse-handling + finalize tail to the no-own-automaton
    // non-leaf case TWICE: once inside the `biggerPropertyAutomaton==null` block
    // (lines 471-485) and once at the shared tail (lines 506-520). The has-own
    // case (lines 487-505) only reaches the shared tail. The second pass over the
    // no-own automaton re-applies the inverse splice in place (finalize is then
    // skipped because the automaton is already stored).
    let first = apply_inverse_and_finalize(
        property,
        bigger,
        individual_automata,
        complete_automata,
        inverse_dependency_graph,
        inverse_map,
        symmetric_properties,
        transitive_properties,
        false,
        building,
    );
    if has_own_automaton {
        first
    } else {
        apply_inverse_and_finalize(
            property,
            first,
            individual_automata,
            complete_automata,
            inverse_dependency_graph,
            inverse_map,
            symmetric_properties,
            transitive_properties,
            false,
            building,
        )
    }
}

/// Port of the inverse-handling + `finalizeConstruction` tail shared by the leaf
/// and non-leaf branches of `buildCompleteAutomataForProperties` (Java 432-446 /
/// 505-524). When `Inv(R)` is anonymous and has its own automaton, the COMPLETE
/// automaton of `Inv(R)` is spliced in (case "a"); otherwise the declared
/// inverses' INDIVIDUAL automata are spliced via `increaseWithDefinedInverseIfNecessary`
/// (case "b"). `unconditional_finalize` reproduces the leaf-with-own-automaton
/// case "b", which finalizes regardless of whether a complete automaton already
/// exists.
#[allow(clippy::too_many_arguments)]
fn apply_inverse_and_finalize(
    property: &ObjectPropExpr,
    mut automaton: Automaton,
    individual_automata: &HashMap<ObjectPropExpr, Automaton>,
    complete_automata: &mut HashMap<ObjectPropExpr, Automaton>,
    inverse_dependency_graph: &Graph<ObjectPropExpr>,
    inverse_map: &HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>>,
    symmetric_properties: &HashSet<ObjectPropExpr>,
    transitive_properties: &HashSet<ObjectPropExpr>,
    unconditional_finalize: bool,
    building: &mut HashSet<ObjectPropExpr>,
) -> Automaton {
    let inv_prop = inverse_property(property);
    // `Inv(R)` is anonymous exactly when `R` is a named property.
    let inverse_is_anonymous = !is_anonymous_property(property);
    if inverse_is_anonymous && individual_automata.contains_key(&inv_prop) {
        let inv_complete = build_complete_automaton(
            &inv_prop,
            individual_automata,
            complete_automata,
            inverse_dependency_graph,
            inverse_map,
            symmetric_properties,
            transitive_properties,
            building,
        );
        increase_automaton_with_inverse(&mut automaton, &mirrored_copy(&inv_complete));
        if !complete_automata.contains_key(property) {
            finalize_construction(
                complete_automata,
                property,
                automaton,
                symmetric_properties,
                transitive_properties,
            );
        }
        // Java 509-512: when `R` is ALREADY in completeAutomata (cached, typically
        // as the bare mirror written by the inverse's `finalizeConstruction` at
        // Java 539 during the `buildCompleteAutomataForProperties(Inv(R))` call
        // above), Java DISCARDS the locally built automaton and adopts the cached
        // one (`biggerPropertyAutomaton = completeAutomata.get(R)`). The local
        // `increaseAutomatonWithInversePropertyAutomaton` mutated a SEPARATE object,
        // so its effect is thrown away. We must NOT write `automaton` back over the
        // cached entry — doing so reinstates a chain-embedded automaton that Java
        // deliberately drops (the EFO_0000784 over-classification bug).
    } else {
        increase_with_defined_inverse_if_necessary(
            property,
            &mut automaton,
            inverse_map,
            individual_automata,
        );
        if unconditional_finalize || !complete_automata.contains_key(property) {
            finalize_construction(
                complete_automata,
                property,
                automaton,
                symmetric_properties,
                transitive_properties,
            );
        }
        // Java 516-519: same as above — adopt the cached automaton, discard the local.
    }
    complete_automata[property].clone()
}
