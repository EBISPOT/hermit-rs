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
// CONSTRUCTION. The automata are built from the role box as a grammar (see
// `RoleBox`) rather than by porting `connectAllAutomata`: HermiT's construction
// depends on `HashMap` iteration order, and its `buildInversePropertiesMap`
// reads `R ⊑ Inv(S)` as if `R` and `S` were declared inverses, so with a
// transitive `S` it propagates `∀R.C` along `Inv(S)`-chains. Inverse roles,
// symmetric and equivalent roles and chains through inverses are all covered by
// closing the inclusions under inverse and building one automaton per class of
// equivalent roles. HermiT's structural regularity checks are kept; an
// irregular role box they miss is rejected when its automata would depend on
// each other. Every complete automaton is stored, spliced and rewritten from
// in its minimal deterministic form (`Automaton::minimized`), so the number of
// clauses a `∀R.C` becomes, and the number of state concepts a node can carry,
// is that of the minimal automaton of `R`'s language. A state that holds of
// every node, as the initial state of a range axiom's `∀R.C` and the final
// states of a domain axiom's `∀R.⊥` do, is eliminated from the clauses
// (`eliminate_universal_states`), so it is never derived node by node.

use std::collections::{HashMap, HashSet};

use horned_owl::model::{Build, ClassExpression as CE, Individual};

use crate::graph::Graph;

use super::automaton::{automata_connector, label_order_key, mirrored_copy, Automaton, State};
use super::owl_axioms::Fact;
use super::{
    inverse_property, is_anonymous_property, ClassExpr, ExpressionManager, ObjectPropExpr,
    OWLAxioms,
};

const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";

/// A canonical, run-stable ordering key for an object-property expression:
/// named properties sort before their inverses, then by IRI. The automata are
/// built in this order so that their state numbering, and therefore the
/// clauses `rewrite_axioms` emits, do not depend on `HashMap` iteration order.
fn prop_sort_key(ope: &ObjectPropExpr) -> (u8, String) {
    label_order_key(ope)
}

pub struct ObjectPropertyInclusionManager {
    automata_by_property: HashMap<ObjectPropExpr, Automaton>,
    /// Whether the role box is irregular in a way HermiT's checks accept, so
    /// that the automata are sound but need not be complete.
    #[cfg_attr(not(test), allow(dead_code))]
    irregular: bool,
    build: Build<super::A>,
    expression_manager: ExpressionManager,
}

impl ObjectPropertyInclusionManager {
    pub(crate) fn automaton(&self, property: &ObjectPropExpr) -> Option<&Automaton> {
        self.automata_by_property.get(property)
    }

    pub(crate) fn restrict_for_property_read_off(&mut self, live: &HashSet<ObjectPropExpr>) {
        for automaton in self.automata_by_property.values_mut() {
            *automaton = automaton.restricted_to_labels(live);
        }
    }

    /// Mirrors `new ObjectPropertyInclusionManager(axioms)`: builds the
    /// per-property automata and records which properties are non-simple in
    /// `axioms.complex_object_property_expressions`.
    pub fn new(axioms: &mut OWLAxioms) -> Result<ObjectPropertyInclusionManager, String> {
        let mut automata_by_property: HashMap<ObjectPropExpr, Automaton> = HashMap::new();
        let irregular = create_automata(&mut automata_by_property, axioms)?;
        Ok(ObjectPropertyInclusionManager {
            automata_by_property,
            irregular,
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
    /// encoding the automaton's states, transitions and final states. State
    /// concepts that hold of every node are then eliminated from the
    /// inclusions ([`eliminate_universal_states`]).
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
        let mut fresh: HashSet<ClassExpr> = HashSet::new();
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
                        fresh.insert(replacement.clone());
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
                    fresh.insert(state_concept.clone());
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
        eliminate_universal_states(axioms, &fresh, CE::Class(self.build.class(OWL_NOTHING)));
        Ok(())
    }
}

/// Removes the state concepts that hold of every node from the inclusions
/// `rewrite_axioms` produced.
///
/// A `∀R.C` that holds of everything, as a range axiom on a complex role does,
/// puts its initial state on every node; a `∀R.⊥`, as the domain axiom
/// `∃R.⊤ ⊑ C` becomes, puts its final states there, and the ε transitions
/// into the normalised terminal state carry that on to the states before them.
/// Such a state is an inclusion `⊤ ⊑ A`, or `⊤ ⊑ A` follows from those of other
/// universal states. Left in, each is derived on every node of every tableau,
/// and every transition clause it occurs in is then matched against that
/// node's edges: a pass over the whole ABox per state per test, for a fact
/// that is never false.
///
/// Since `A` is true of every node, a disjunction containing `A`, or `∀S.A`, is
/// a tautology and goes; `¬A` is a false disjunct and goes; `∀S.¬A` is
/// `∀S.⊥`. A transition from a universal state thus fires on its edge alone,
/// and the state itself is never asserted. Only the concepts this call minted
/// are considered, so a class of the ontology is left as written.
fn eliminate_universal_states(
    axioms: &mut OWLAxioms,
    fresh: &HashSet<ClassExpr>,
    owl_nothing: ClassExpr,
) {
    // The universal states: asserted of ⊤ outright, or implied by other
    // universal states through an inclusion whose other disjuncts are their
    // complements.
    let mut universal: HashSet<ClassExpr> = HashSet::new();
    loop {
        let mut changed = false;
        for inclusion in &axioms.concept_inclusions {
            let mut positive: Option<&ClassExpr> = None;
            let mut implied = true;
            for disjunct in inclusion {
                match disjunct {
                    CE::Class(_) if positive.is_none() && fresh.contains(disjunct) => {
                        positive = Some(disjunct);
                    }
                    CE::ObjectComplementOf(inner) if universal.contains(&**inner) => {}
                    _ => {
                        implied = false;
                        break;
                    }
                }
            }
            if let (true, Some(state)) = (implied, positive) {
                if !universal.contains(state) {
                    universal.insert(state.clone());
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    if universal.is_empty() {
        return;
    }
    let inclusions = std::mem::take(&mut axioms.concept_inclusions);
    for inclusion in inclusions {
        let mut kept: Vec<ClassExpr> = Vec::with_capacity(inclusion.len());
        let mut tautology = false;
        for disjunct in inclusion {
            match &disjunct {
                CE::Class(_) if universal.contains(&disjunct) => {
                    tautology = true;
                    break;
                }
                CE::ObjectComplementOf(inner) if universal.contains(&**inner) => {}
                CE::ObjectAllValuesFrom { bce, .. } if universal.contains(&**bce) => {
                    tautology = true;
                    break;
                }
                CE::ObjectAllValuesFrom { ope, bce } => match &**bce {
                    CE::ObjectComplementOf(inner) if universal.contains(&**inner) => {
                        kept.push(CE::ObjectAllValuesFrom {
                            ope: ope.clone(),
                            bce: Box::new(owl_nothing.clone()),
                        });
                    }
                    _ => kept.push(disjunct),
                },
                _ => kept.push(disjunct),
            }
        }
        if tautology {
            continue;
        }
        if kept.is_empty() {
            // Every disjunct was the complement of a universal state: ⊤ ⊑ ⊥.
            kept.push(owl_nothing.clone());
        }
        axioms.concept_inclusions.push(kept);
    }
}

fn is_owl_thing(ce: &ClassExpr) -> bool {
    matches!(ce, CE::Class(c) if c.0.to_string() == OWL_THING)
}

fn is_owl_nothing(ce: &ClassExpr) -> bool {
    matches!(ce, CE::Class(c) if c.0.to_string() == OWL_NOTHING)
}

// ---------------------------------------------------------------------------
// Automaton construction.
// ---------------------------------------------------------------------------

/// Builds the automata of the non-simple properties. Returns whether the role
/// box turned out to be irregular in a way HermiT's checks accept (see
/// `RoleBox::complete_automaton`).
fn create_automata(
    automata_by_property: &mut HashMap<ObjectPropExpr, Automaton>,
    axioms: &mut OWLAxioms,
) -> Result<bool, String> {
    let simple: Vec<[ObjectPropExpr; 2]> = axioms.simple_object_property_inclusions.clone();
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

    // HermiT's structural regularity checks, kept so that the same role boxes
    // are rejected with the same message.
    let equivalent = find_equivalent_properties(&simple);
    let property_dependency_graph = build_property_ordering(&simple, &complex, &equivalent)?;
    check_for_regularity(&property_dependency_graph, &equivalent)?;

    let role_box = RoleBox::new(&simple, &complex);
    let mut non_simple: Vec<ObjectPropExpr> = role_box.non_simple.iter().cloned().collect();
    non_simple.sort_by_key(prop_sort_key);
    let mut building: HashSet<ObjectPropExpr> = HashSet::new();
    let mut irregular = false;
    for property in &non_simple {
        role_box.complete_automaton(property, automata_by_property, &mut building, &mut irregular);
        axioms.complex_object_property_expressions.insert(property.clone());
    }

    // Java always constructs an automaton for owl:topObjectProperty since it
    // might occur in queries (the axiomatisation at query time fails
    // otherwise): an initial -> final transition on the top role plus an ε
    // loop (transitivity). See buildIndividualAutomata ~lines 784-800.
    let top = top_object_property();
    if !automata_by_property.contains_key(&top) {
        let mut automaton = Automaton::new();
        let initial = automaton.add_state(true, false);
        let finalst = automaton.add_state(false, true);
        automaton.add_transition(initial, Some(top.clone()), finalst);
        automaton.add_transition(finalst, None, initial);
        automata_by_property.insert(inverse_property(&top), mirrored_copy(&automaton));
        automata_by_property.insert(top, automaton);
    }
    Ok(irregular)
}

/// The role box as a grammar: `w ⊑ R` holds exactly when `R` derives the word
/// `w` from the told inclusions closed under inverse (`S1...Sn ⊑ R` also gives
/// `Inv(Sn)...Inv(S1) ⊑ Inv(R)`). The automaton of a non-simple `R` accepts
/// exactly the words `R` derives through chain inclusions; the tableau's
/// role-inclusion clauses supply the simple hierarchy on each edge, so a simple
/// sub-property needs no transition of its own.
///
/// This replaces HermiT's `connectAllAutomata`, whose output depends on
/// `HashMap` iteration order and which treats `R ⊑ Inv(S)` as if `R` and `S`
/// were declared inverses (`buildInversePropertiesMap`): with a transitive `S`
/// that made `∀R.C` propagate along `Inv(S)`-chains, i.e. `Inv(S) ⊑ R`, which
/// does not follow. The construction here is the one of Horrocks, Kutz and
/// Sattler ("The Even More Irresistible SROIQ", KR 2006), over classes of
/// equivalent roles.
struct RoleBox {
    /// `supers[X]`: the reflexive-transitive closure of the simple inclusions
    /// (closed under inverse) above `X`.
    supers: HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>>,
    /// Simple inclusions closed under inverse, in a fixed order.
    inclusions: Vec<[ObjectPropExpr; 2]>,
    /// Chain inclusions (length ≥ 2) closed under inverse, in a fixed order.
    chains: Vec<(Vec<ObjectPropExpr>, ObjectPropExpr)>,
    /// Roles with a chain inclusion below them, closed under inverse.
    non_simple: HashSet<ObjectPropExpr>,
}

impl RoleBox {
    fn new(
        simple: &[[ObjectPropExpr; 2]],
        complex: &[(Vec<ObjectPropExpr>, ObjectPropExpr)],
    ) -> RoleBox {
        let mut inclusions: Vec<[ObjectPropExpr; 2]> = Vec::new();
        for [sub, sup] in simple {
            for inclusion in [
                [sub.clone(), sup.clone()],
                [inverse_property(sub), inverse_property(sup)],
            ] {
                if inclusion[0] != inclusion[1] && !inclusions.contains(&inclusion) {
                    inclusions.push(inclusion);
                }
            }
        }
        let mut chains: Vec<(Vec<ObjectPropExpr>, ObjectPropExpr)> = Vec::new();
        for (subs, sup) in complex {
            let mirrored: Vec<ObjectPropExpr> = subs.iter().rev().map(inverse_property).collect();
            for chain in [(subs.clone(), sup.clone()), (mirrored, inverse_property(sup))] {
                if !chains.contains(&chain) {
                    chains.push(chain);
                }
            }
        }
        let mut direct: HashMap<ObjectPropExpr, Vec<ObjectPropExpr>> = HashMap::new();
        for [sub, sup] in &inclusions {
            direct.entry(sub.clone()).or_default().push(sup.clone());
        }
        let mut roles: HashSet<ObjectPropExpr> = HashSet::new();
        for [sub, sup] in &inclusions {
            roles.insert(sub.clone());
            roles.insert(sup.clone());
        }
        for (subs, sup) in &chains {
            roles.extend(subs.iter().cloned());
            roles.insert(sup.clone());
        }
        let mut supers: HashMap<ObjectPropExpr, HashSet<ObjectPropExpr>> = HashMap::new();
        for role in &roles {
            let mut reached: HashSet<ObjectPropExpr> = HashSet::from([role.clone()]);
            let mut pending = vec![role.clone()];
            while let Some(current) = pending.pop() {
                for sup in direct.get(&current).into_iter().flatten() {
                    if reached.insert(sup.clone()) {
                        pending.push(sup.clone());
                    }
                }
            }
            supers.insert(role.clone(), reached);
        }
        let mut non_simple: HashSet<ObjectPropExpr> = HashSet::new();
        for (_, sup) in &chains {
            non_simple.extend(supers[sup].iter().cloned());
        }
        RoleBox { supers, inclusions, chains, non_simple }
    }

    fn is_sub_property(&self, sub: &ObjectPropExpr, sup: &ObjectPropExpr) -> bool {
        sub == sup || self.supers.get(sub).is_some_and(|s| s.contains(sup))
    }

    /// Whether `a` and `b` are equivalent, so that `L(a) = L(b)`.
    fn equivalent(&self, a: &ObjectPropExpr, b: &ObjectPropExpr) -> bool {
        self.is_sub_property(a, b) && self.is_sub_property(b, a)
    }

    /// The automaton accepting the words `property` derives, memoised in
    /// `complete`. A non-simple role of another class, which is smaller in the
    /// regular order, is spliced in as its own complete automaton.
    ///
    /// HermiT's structural checks accept some role boxes whose classes depend
    /// on each other (through equivalences or inverses those checks do not
    /// close over); their languages need not be regular. There the dependency
    /// is cut and the role is kept as a plain label: every accepted word is
    /// still entailed, and `irregular` records that completeness is not
    /// guaranteed, as it is not in HermiT.
    fn complete_automaton(
        &self,
        property: &ObjectPropExpr,
        complete: &mut HashMap<ObjectPropExpr, Automaton>,
        building: &mut HashSet<ObjectPropExpr>,
        irregular: &mut bool,
    ) -> Automaton {
        if let Some(automaton) = complete.get(property) {
            return automaton.clone();
        }
        if is_anonymous_property(property) {
            // `L(Inv(R))` is the mirror of `L(R)`.
            let named = inverse_property(property);
            if building.contains(&named) {
                *irregular = true;
                return single_transition_automaton(property);
            }
            let automaton =
                mirrored_copy(&self.complete_automaton(&named, complete, building, irregular))
                    .minimized();
            complete.insert(property.clone(), automaton.clone());
            return automaton;
        }
        if building.contains(property) {
            *irregular = true;
            return single_transition_automaton(property);
        }
        building.insert(property.clone());
        let in_class = |role: &ObjectPropExpr| self.equivalent(role, property);

        // The skeleton: `initial -R-> final` plus one path per inclusion into
        // the class of `R`, where an occurrence of the class itself at the start
        // (end) of a chain becomes the final (initial) state.
        let mut automaton = Automaton::new();
        let initial = automaton.add_state(true, false);
        let finalst = automaton.add_state(false, true);
        let mut transitions: Vec<(State, Option<ObjectPropExpr>, State)> =
            vec![(initial, Some(property.clone()), finalst)];
        for [sub, sup] in &self.inclusions {
            // A simple sub-property is covered by the role-inclusion clauses.
            if in_class(sup) && !in_class(sub) && self.non_simple.contains(sub) {
                transitions.push((initial, Some(sub.clone()), finalst));
            }
        }
        for (subs, sup) in &self.chains {
            if !in_class(sup) {
                continue;
            }
            let n = subs.len();
            let starts_in_class = in_class(&subs[0]);
            let ends_in_class = in_class(&subs[n - 1]);
            let middle = &subs[usize::from(starts_in_class)..n - usize::from(ends_in_class)];
            let from = if starts_in_class { finalst } else { initial };
            let to = if ends_in_class { initial } else { finalst };
            if middle.is_empty() {
                // `R ∘ R ⊑ R`: transitivity.
                transitions.push((from, None, to));
                continue;
            }
            let mut current = from;
            for (index, role) in middle.iter().enumerate() {
                let next = if index + 1 == middle.len() {
                    to
                } else {
                    automaton.add_state(false, false)
                };
                transitions.push((current, Some(role.clone()), next));
                current = next;
            }
        }

        // Substitute each non-simple role by its automaton. A role of this
        // class occurs inside a chain only in an irregular role box.
        for (from, label, to) in transitions {
            match label {
                Some(role) if in_class(&role) && !(from == initial && to == finalst) => {
                    *irregular = true;
                    automaton.add_transition(from, Some(role), to);
                }
                Some(role) if !in_class(&role) && self.non_simple.contains(&role) => {
                    let smaller = self.complete_automaton(&role, complete, building, irregular);
                    automata_connector(&mut automaton, &smaller, from, to);
                }
                label => automaton.add_transition(from, label, to),
            }
        }
        building.remove(property);
        // The skeleton with its splices accepts the right words but repeats
        // whole sub-automata for every occurrence of a role, and those copies
        // multiply through every splice above them. Only the language matters
        // to the clauses, so each complete automaton is the minimal
        // deterministic one: `∀R.C` then costs one concept per state of that
        // automaton, and every automaton spliced in higher up is small too.
        let automaton = automaton.minimized();
        complete.insert(property.clone(), automaton.clone());
        automaton
    }
}

fn single_transition_automaton(property: &ObjectPropExpr) -> Automaton {
    let mut automaton = Automaton::new();
    let initial = automaton.add_state(true, false);
    let finalst = automaton.add_state(false, true);
    automaton.add_transition(initial, Some(property.clone()), finalst);
    automaton
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

/// The `owl:topObjectProperty` expression (Java's
/// `df.getOWLTopObjectProperty()`).
fn top_object_property() -> ObjectPropExpr {
    let build: Build<super::A> = Build::new_arc();
    ObjectPropExpr::ObjectProperty(
        build.object_property("http://www.w3.org/2002/07/owl#topObjectProperty"),
    )
}

/// Brute-force cross-check of the role automata against the RBox they encode.
///
/// For regular RBoxes of inclusions (no reflexivity), a role word `w` is a
/// sub-role of `P` exactly when `P` derives `w` in the grammar of the RBox's
/// inclusions closed under inverse (`S1...Sn ⊑ R` also gives
/// `Inv(Sn)...Inv(S1) ⊑ Inv(R)`): `∀P.C` is propagated along walks, so a
/// word such as `R Inv(R) R` is a walk even where the model folds it back.
/// A `∀P.C` restriction propagates along the words `P`'s automaton accepts,
/// widened letter by letter by the simple role hierarchy, which the tableau's
/// role-inclusion clauses apply. So, for every random RBox and every word up to
/// a bounded length:
/// * every word the automaton accepts is derivable (soundness);
/// * every derivable word is covered by an accepted word (completeness), and
///   a property without an automaton derives only single letters.
#[cfg(test)]
mod language_tests {
    use super::*;
    use horned_owl::model::{
        Component, EquivalentObjectProperties, InverseObjectProperties, MutableOntology,
        ObjectPropertyDomain, ObjectPropertyRange, SubObjectPropertyExpression as SOPE,
        SubObjectPropertyOf, SymmetricObjectProperty, TransitiveObjectProperty,
    };
    use horned_owl::ontology::set::SetOntology;

    use crate::structural::OWLNormalization;

    const ROLES: usize = 3;
    const MAX_LENGTH: usize = 4;

    /// Letter `2i` is role `i`, letter `2i + 1` its inverse.
    struct Grammar {
        letters: Vec<ObjectPropExpr>,
        /// `up[l]`: the letters reachable from `l` by simple inclusions,
        /// reflexively and transitively.
        up: Vec<HashSet<usize>>,
        chains: Vec<(Vec<usize>, usize)>,
    }

    impl Grammar {
        fn letter(&self, ope: &ObjectPropExpr) -> usize {
            self.letters.iter().position(|l| l == ope).expect("letter")
        }

        fn new(letters: Vec<ObjectPropExpr>, axioms: &OWLAxioms) -> Grammar {
            let mut grammar = Grammar { up: Vec::new(), chains: Vec::new(), letters };
            let n = grammar.letters.len();
            let mut up: Vec<HashSet<usize>> = (0..n).map(|l| HashSet::from([l])).collect();
            for [sub, sup] in &axioms.simple_object_property_inclusions {
                let (sub, sup) = (grammar.letter(sub), grammar.letter(sup));
                up[sub].insert(sup);
                up[sub ^ 1].insert(sup ^ 1);
            }
            loop {
                let mut changed = false;
                for l in 0..n {
                    for m in up[l].clone() {
                        for k in up[m].clone() {
                            changed |= up[l].insert(k);
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            grammar.up = up;
            for inclusion in &axioms.complex_object_property_inclusions {
                let subs: Vec<usize> = inclusion
                    .sub_object_properties
                    .iter()
                    .map(|s| grammar.letter(s))
                    .collect();
                let sup = grammar.letter(&inclusion.super_object_property);
                let mirrored = subs.iter().rev().map(|s| s ^ 1).collect();
                grammar.chains.push((subs, sup));
                grammar.chains.push((mirrored, sup ^ 1));
            }
            grammar
        }

        /// The letters deriving each factor `w[i..j]`, indexed `[i][j]`.
        fn derivations(&self, word: &[usize]) -> Vec<Vec<HashSet<usize>>> {
            let n = word.len();
            let mut table = vec![vec![HashSet::new(); n + 1]; n + 1];
            for length in 1..=n {
                for i in 0..=n - length {
                    let j = i + length;
                    let mut direct: HashSet<usize> = HashSet::new();
                    if length == 1 {
                        direct.insert(word[i]);
                    }
                    for (subs, sup) in &self.chains {
                        if subs.len() <= length && Self::splits(&table, subs, i, j) {
                            direct.insert(*sup);
                        }
                    }
                    table[i][j] = direct.iter().flat_map(|l| self.up[*l].iter().copied()).collect();
                }
            }
            table
        }

        /// Whether `w[i..j]` splits into non-empty factors derived by `subs`.
        fn splits(table: &[Vec<HashSet<usize>>], subs: &[usize], i: usize, j: usize) -> bool {
            match subs {
                [] => i == j,
                [last] => i < j && table[i][j].contains(last),
                [first, rest @ ..] => (i + 1..j)
                    .any(|k| table[i][k].contains(first) && Self::splits(table, rest, k, j)),
            }
        }
    }

    /// Whether `automaton` accepts a word whose `i`-th label is one of `word[i]`.
    fn accepts(automaton: &Automaton, word: &[HashSet<ObjectPropExpr>]) -> bool {
        let mut pending: Vec<(State, usize)> =
            automaton.initials().into_iter().map(|s| (s, 0)).collect();
        let mut seen = HashSet::new();
        let delta = automaton.delta();
        while let Some((state, position)) = pending.pop() {
            if !seen.insert((state, position)) {
                continue;
            }
            if position == word.len() && automaton.is_terminal(state) {
                return true;
            }
            for transition in delta.iter().filter(|t| t.start == state) {
                match &transition.label {
                    None => pending.push((transition.end, position)),
                    Some(label) if word.get(position).is_some_and(|w| w.contains(label)) => {
                        pending.push((transition.end, position + 1))
                    }
                    Some(_) => {}
                }
            }
        }
        false
    }

    /// A small xorshift generator: the cases are reproducible from the seed.
    struct Random(u64);

    impl Random {
        fn below(&mut self, n: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % n as u64) as usize
        }
    }

    fn random_rbox(random: &mut Random, letters: &[ObjectPropExpr]) -> (Vec<String>, SetOntology<super::super::A>) {
        let mut ontology: SetOntology<super::super::A> = SetOntology::new();
        let mut shown = Vec::new();
        let letter = |random: &mut Random| letters[random.below(letters.len())].clone();
        for _ in 0..1 + random.below(5) {
            let component = match random.below(8) {
                0 | 1 => Component::SubObjectPropertyOf(SubObjectPropertyOf {
                    sub: SOPE::ObjectPropertyExpression(letter(random)),
                    sup: letter(random),
                }),
                2 | 3 => Component::TransitiveObjectProperty(TransitiveObjectProperty(letter(random))),
                4 | 5 => {
                    let length = 2 + random.below(2);
                    Component::SubObjectPropertyOf(SubObjectPropertyOf {
                        sub: SOPE::ObjectPropertyChain((0..length).map(|_| letter(random)).collect()),
                        sup: letter(random),
                    })
                }
                6 => Component::InverseObjectProperties(InverseObjectProperties(
                    letter(random),
                    letter(random),
                )),
                _ => match random.below(2) {
                    0 => Component::SymmetricObjectProperty(SymmetricObjectProperty(letter(random))),
                    _ => Component::EquivalentObjectProperties(EquivalentObjectProperties(vec![
                        letter(random),
                        letter(random),
                    ])),
                },
            };
            shown.push(format!("{component:?}"));
            ontology.insert(component);
        }
        (shown, ontology)
    }

    fn words(letters: usize) -> Vec<Vec<usize>> {
        let mut result: Vec<Vec<usize>> = vec![Vec::new()];
        let mut frontier = result.clone();
        for _ in 0..MAX_LENGTH {
            frontier = frontier
                .iter()
                .flat_map(|w| (0..letters).map(move |l| [w.clone(), vec![l]].concat()))
                .collect();
            result.extend(frontier.iter().cloned());
        }
        result
    }

    /// Checks one RBox, returning the first unsound and the first incomplete
    /// word found, if any, and whether completeness was checked at all.
    fn check(
        ontology: &SetOntology<super::super::A>,
        letters: &[ObjectPropExpr],
    ) -> (Option<String>, Option<String>, bool) {
        let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
        normalization.process_ontology(ontology).expect("normalize");
        let mut axioms = normalization.into_axioms();
        let grammar = Grammar::new(letters.to_vec(), &axioms);
        // HermiT's structural checks reject many irregular role boxes.
        let Ok(manager) = ObjectPropertyInclusionManager::new(&mut axioms) else {
            return (None, None, false);
        };
        let (mut unsound, mut incomplete) = (None, None);
        let show = |word: &[usize]| -> Vec<String> {
            word.iter().map(|l| format!("{:?}", letters[*l])).collect()
        };
        for word in words(letters.len()) {
            let table = grammar.derivations(&word);
            let derived: HashSet<usize> =
                if word.is_empty() { HashSet::new() } else { table[0][word.len()].clone() };
            let exact: Vec<HashSet<ObjectPropExpr>> =
                word.iter().map(|l| HashSet::from([letters[*l].clone()])).collect();
            let widened: Vec<HashSet<ObjectPropExpr>> = word
                .iter()
                .map(|l| grammar.up[*l].iter().map(|u| letters[*u].clone()).collect())
                .collect();
            for (index, property) in letters.iter().enumerate() {
                let entailed = derived.contains(&index);
                match manager.automaton(property) {
                    Some(automaton) => {
                        if unsound.is_none() && !entailed && accepts(automaton, &exact) {
                            unsound = Some(format!("{:?} accepts {:?}", property, show(&word)));
                        }
                        if incomplete.is_none()
                            && !manager.irregular
                            && entailed
                            && !accepts(automaton, &widened)
                        {
                            incomplete = Some(format!("{:?} misses {:?}", property, show(&word)));
                        }
                    }
                    None if incomplete.is_none() && !manager.irregular && entailed && word.len() > 1 => {
                        incomplete = Some(format!(
                            "incomplete: {:?} has no automaton but derives {:?}",
                            property,
                            show(&word)
                        ));
                    }
                    None => {}
                }
            }
        }
        (unsound, incomplete, !manager.irregular)
    }

    fn letters() -> Vec<ObjectPropExpr> {
        let build: Build<super::super::A> = Build::new_arc();
        (0..ROLES)
            .flat_map(|i| {
                let named = ObjectPropExpr::ObjectProperty(build.object_property(format!("http://ex/r{i}")));
                [named.clone(), inverse_property(&named)]
            })
            .collect()
    }

    /// `located_in ∘ part_of ⊑ located_in`, `part_of ∘ located_in ⊑ located_in`,
    /// both transitive: the language of `located_in` is `part_of* located_in
    /// (located_in | part_of)*`, two states, and that of `part_of` is
    /// `part_of+`, two states. Spliced together without minimisation they are
    /// six states with ε cycles.
    #[test]
    fn automata_are_minimal() {
        let letters = letters();
        let (located_in, part_of) = (&letters[0], &letters[2]);
        let mut ontology: SetOntology<super::super::A> = SetOntology::new();
        for role in [located_in, part_of] {
            ontology.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(role.clone())));
        }
        for chain in [vec![located_in.clone(), part_of.clone()], vec![part_of.clone(), located_in.clone()]] {
            ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
                sub: SOPE::ObjectPropertyChain(chain),
                sup: located_in.clone(),
            }));
        }
        assert_eq!(check(&ontology, &letters), (None, None, true));
        let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
        normalization.process_ontology(&ontology).expect("normalize");
        let mut axioms = normalization.into_axioms();
        let manager = ObjectPropertyInclusionManager::new(&mut axioms).expect("regular");
        let size = |role: &ObjectPropExpr| {
            let automaton = manager.automaton(role).expect("automaton");
            (automaton.states().len(), automaton.delta().len())
        };
        assert_eq!(size(located_in), (2, 4));
        assert_eq!(size(part_of), (2, 2));
        assert_eq!(size(&inverse_property(located_in)), (2, 4));
        assert_eq!(size(&inverse_property(part_of)), (2, 2));
    }

    /// `⊤ ⊑ ∀R.C` holds its initial state of every node and `∃R.⊤ ⊑ D` its
    /// final states, so neither is written into a clause: the transitions out
    /// of the initial state and into the final states fire on their edge alone.
    #[test]
    fn universal_states_are_eliminated() {
        let letters = letters();
        let (r, p) = (&letters[0], &letters[2]);
        let build: Build<super::super::A> = Build::new_arc();
        let class = |name: &str| CE::Class(build.class(format!("http://ex/{name}")));
        let mut ontology: SetOntology<super::super::A> = SetOntology::new();
        ontology.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(r.clone())));
        ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
            sub: SOPE::ObjectPropertyChain(vec![p.clone(), r.clone()]),
            sup: r.clone(),
        }));
        ontology.insert(Component::ObjectPropertyRange(ObjectPropertyRange {
            ope: r.clone(),
            ce: class("C"),
        }));
        ontology.insert(Component::ObjectPropertyDomain(ObjectPropertyDomain {
            ope: r.clone(),
            ce: class("D"),
        }));
        let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
        normalization.process_ontology(&ontology).expect("normalize");
        let mut axioms = normalization.into_axioms();
        let manager = ObjectPropertyInclusionManager::new(&mut axioms).expect("regular");
        manager.rewrite_axioms(&mut axioms, 0).expect("rewrite");
        let is_state = |ce: &ClassExpr| {
            matches!(ce, CE::Class(c) if c.0.to_string().starts_with("internal:all#"))
        };
        let inclusions = &axioms.concept_inclusions;
        // No state is asserted of ⊤ or of another state alone.
        assert!(!inclusions.iter().any(|inclusion| inclusion.iter().all(|d| {
            is_state(d) || matches!(d, CE::ObjectComplementOf(inner) if is_state(inner))
        })));
        // The range: an R edge puts its target in the state after the initial one.
        assert!(inclusions.iter().any(|inclusion| matches!(
            inclusion.as_slice(),
            [CE::ObjectAllValuesFrom { ope, bce }] if ope == r && is_state(bce)
        )));
        // The domain: an R edge puts its source in the state before the final one.
        assert!(inclusions.iter().any(|inclusion| matches!(
            inclusion.as_slice(),
            [state, CE::ObjectAllValuesFrom { ope, bce }]
                if is_state(state) && ope == r && is_owl_nothing(bce)
        )));
        // The classes the axioms name are still reached from a state.
        for name in ["C", "D"] {
            let class = class(name);
            assert!(
                inclusions.iter().any(|inclusion| {
                    inclusion.len() == 2
                        && inclusion.contains(&class)
                        && inclusion.iter().any(|d| {
                            matches!(d, CE::ObjectComplementOf(state) if is_state(state))
                        })
                }),
                "{name}"
            );
        }
    }

    #[test]
    fn inverse_super_property_of_transitive_role_is_not_a_sub_property() {
        let letters = letters();
        let mut ontology: SetOntology<super::super::A> = SetOntology::new();
        ontology.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(
            letters[2].clone(),
        )));
        ontology.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
            sub: SOPE::ObjectPropertyExpression(letters[0].clone()),
            sup: letters[3].clone(),
        }));
        assert_eq!(check(&ontology, &letters), (None, None, true));
    }

    #[test]
    fn automata_accept_exactly_the_entailed_role_words() {
        let letters = letters();
        let mut random = Random(0x9e37_79b9_7f4a_7c15);
        let mut failures = Vec::new();
        let mut regular = 0;
        for case in 0..1500 {
            let (shown, ontology) = random_rbox(&mut random, &letters);
            let (unsound, incomplete, checked) = check(&ontology, &letters);
            regular += usize::from(checked);
            if let Some(failure) = unsound {
                failures.push(format!("case {case}: unsound: {failure}\n  {}", shown.join("\n  ")));
            }
            if let Some(failure) = incomplete {
                failures.push(format!("case {case}: incomplete: {failure}\n  {}", shown.join("\n  ")));
            }
        }
        assert!(failures.is_empty(), "{} failures:\n{}", failures.len(), failures.join("\n"));
        // Most random role boxes are regular, so completeness is exercised.
        assert!(regular > 800, "only {regular} regular role boxes");
    }
}
