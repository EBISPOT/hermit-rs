// Port of org.semanticweb.HermiT.tableau.HyperresolutionManager (the clause-
// application driver) plus a minimal saturation loop.
//
// HermiT indexes compiled clauses by their delta predicate (with extra
// guard-concept optimizations for atomic roles) and, on each delta tuple, runs
// the matching evaluators. This port keeps the essential structure -- clauses
// sharing a body are grouped (DLClauseBodyKey) into one evaluator per swapped
// delta body atom, indexed by that atom's predicate -- without the guard-concept
// optimizations (which only affect performance, not results).
//
// SCOPE: this drives Horn-style derivation (rule application + clash). The
// `saturate` method here is a Horn-only fixpoint -- existential expansion and
// disjunction branching are handled by `run_calculus` in `src/reasoner.rs`,
// which calls into this manager as one phase of the full tableau loop.
// `saturate` is used by the Datalog engine for ontologies that need only the
// rule-application fixpoint (no existential expansion or disjunctions).
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::model::term::Variable;
use crate::model::{Atom, AtomicConcept, AtomicRole, Concept, DLClause, DLPredicate};
use crate::tableau::dependency_set::PermanentDependencySet;
use crate::tableau::dl_clause_evaluator::DLClauseEvaluator;
use crate::tableau::extension_table::View;
use crate::tableau::hyperresolution::ValuesBufferManager;
use crate::tableau::node::NodeId;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;

/// A compiled clause evaluator shared between the by-delta-predicate list and the
/// guard-concept index (HermiT shares one `DLClauseEvaluator` instance across the
/// `CompiledDLClauseInfo` nodes of its several lists).
type SharedEvaluator = Rc<RefCell<DLClauseEvaluator>>;

fn is_predicate_with_extension(predicate: &DLPredicate) -> bool {
    !matches!(predicate, DLPredicate::NodeIdLessEqualThan)
        && !matches!(predicate, DLPredicate::NodeIDsAscendingOrEqual(_))
}

/// Maps a stored extension-table label back to the DL predicate used to index
/// evaluators (atomic concepts are stored under the `Concept` label).
fn label_to_predicate(object: &TableauObject) -> Option<DLPredicate> {
    match object {
        TableauObject::DLPredicate(p) => Some(p.clone()),
        TableauObject::Concept(c) => match c {
            Concept::AtomicConcept(a) => Some(DLPredicate::AtomicConcept(a.clone())),
            Concept::AtLeastConcept(a) => Some(DLPredicate::AtLeastConcept(a.clone())),
            Concept::AtLeastDataRange(a) => Some(DLPredicate::AtLeastDataRange(a.clone())),
            Concept::ExistsDescriptionGraph(e) => {
                Some(DLPredicate::ExistsDescriptionGraph(e.clone()))
            }
            Concept::AtomicNegationConcept(_) => None,
        },
        _ => None,
    }
}

/// `getAtomGoodness` from HermiT's `BodyAtomsSwapper`: scores how good a
/// candidate next body atom is, given the variables already bound by atoms
/// placed earlier. Higher is better. The special `NodeIDLessEqualThan` and
/// `NodeIDsAscendingOrEqual` comparison atoms are heavily penalized until all
/// their variables are bound, so they are never placed before the atoms that
/// bind their variables (otherwise the evaluator would read an unbound
/// variable and panic).
fn get_atom_goodness(
    atom: &Atom,
    bound_variables: &HashSet<Variable>,
    node_id_comparison_atoms: &[Atom],
) -> i32 {
    let predicate = atom.get_dl_predicate();
    if matches!(predicate, DLPredicate::NodeIdLessEqualThan) {
        let arg0_bound = atom
            .get_argument_variable(0)
            .is_some_and(|v| bound_variables.contains(v));
        let arg1_bound = atom
            .get_argument_variable(1)
            .is_some_and(|v| bound_variables.contains(v));
        if arg0_bound && arg1_bound {
            1000
        } else {
            -2000
        }
    } else if matches!(predicate, DLPredicate::NodeIDsAscendingOrEqual(_)) {
        let mut number_of_unbound_variables = 0;
        for argument_index in (0..atom.get_arity()).rev() {
            if let Some(variable) = atom.get_argument(argument_index).as_variable() {
                if !bound_variables.contains(variable) {
                    number_of_unbound_variables += 1;
                }
            }
        }
        if number_of_unbound_variables > 0 {
            -5000
        } else {
            5000
        }
    } else {
        let mut number_of_bound_variables = 0;
        let mut number_of_unbound_variables = 0;
        for argument_index in (0..atom.get_arity()).rev() {
            if let Some(variable) = atom.get_argument(argument_index).as_variable() {
                if bound_variables.contains(variable) {
                    number_of_bound_variables += 1;
                } else {
                    number_of_unbound_variables += 1;
                }
            }
        }
        let mut goodness = number_of_bound_variables * 100 - number_of_unbound_variables * 10;
        if predicate.arity() == 2
            && number_of_unbound_variables == 1
            && !node_id_comparison_atoms.is_empty()
        {
            // The single unbound variable of this binary atom: pick argument 0
            // unless it is already bound, in which case argument 1 is the
            // unbound one.
            let mut unbound_variable = atom.get_argument_variable(0);
            if unbound_variable.is_some_and(|v| bound_variables.contains(v)) {
                unbound_variable = atom.get_argument_variable(1);
            }
            if let Some(unbound_variable) = unbound_variable {
                for compare_atom in node_id_comparison_atoms.iter().rev() {
                    let argument0 = compare_atom.get_argument_variable(0);
                    let argument1 = compare_atom.get_argument_variable(1);
                    let arg0_ok = argument0.is_some_and(|a| {
                        bound_variables.contains(a) || unbound_variable == a
                    });
                    let arg1_ok = argument1.is_some_and(|a| {
                        bound_variables.contains(a) || unbound_variable == a
                    });
                    if arg0_ok && arg1_ok {
                        goodness += 5;
                        break;
                    }
                }
            }
        }
        goodness
    }
}

/// Port of HermiT's `BodyAtomsSwapper.getSwappedDLClause`: puts body atom
/// `index` (the delta atom) at position 0, then greedily reorders the remaining
/// body atoms by `getAtomGoodness` so that variables are bound before they are
/// used. This is a faithful (full goodness) port, not just the minimal
/// binding-safe ordering.
fn swap_body_to_front(dl_clause: &DLClause, index: usize) -> DLClause {
    let body: Vec<Atom> = dl_clause.get_body_atoms();
    let length = body.len();

    // Collect the NodeIDLessEqualThan comparison atoms still to be placed, and
    // mark which atoms have been used (iterating in reverse, mirroring Java).
    let mut node_id_comparison_atoms: Vec<Atom> = Vec::with_capacity(length);
    for atom in body.iter().rev() {
        if matches!(atom.get_dl_predicate(), DLPredicate::NodeIdLessEqualThan) {
            node_id_comparison_atoms.push(atom.clone());
        }
    }

    let mut used_atoms = vec![false; length];
    let mut reordered_atoms: Vec<Atom> = Vec::with_capacity(length);
    let mut bound_variables: HashSet<Variable> = HashSet::new();

    // The chosen delta atom goes first, binding its variables.
    let delta = &body[index];
    delta.get_variables(&mut bound_variables);
    reordered_atoms.push(delta.clone());
    used_atoms[index] = true;

    while reordered_atoms.len() != length {
        let mut best_atom_index: i32 = -1;
        let mut best_atom_goodness = -1000;
        // Iterate in reverse so that, among equal-goodness atoms, the earliest
        // (lowest index) wins -- matching Java's `>` comparison over a
        // descending index loop.
        for current_index in (0..length).rev() {
            if !used_atoms[current_index] {
                let atom = &body[current_index];
                let atom_goodness =
                    get_atom_goodness(atom, &bound_variables, &node_id_comparison_atoms);
                if atom_goodness > best_atom_goodness {
                    best_atom_goodness = atom_goodness;
                    best_atom_index = current_index as i32;
                }
            }
        }
        let best_atom_index = best_atom_index as usize;
        let best_atom = body[best_atom_index].clone();
        used_atoms[best_atom_index] = true;
        best_atom.get_variables(&mut bound_variables);
        if let Some(pos) = node_id_comparison_atoms.iter().position(|a| a == &best_atom) {
            node_id_comparison_atoms.remove(pos);
        }
        reordered_atoms.push(best_atom);
    }

    DLClause::create(dl_clause.get_head_atoms(), reordered_atoms)
}

/// Port of `HyperresolutionManager.getAtomicRoleClauseGuards`: for a swapped
/// clause whose delta (body atom 0) is an atomic role `r(X,Y)`, collect the
/// atomic-concept body atoms guarding `X` (returned first) and `Y` (returned
/// second). Note Java increments the body index twice per iteration (a `for`
/// step plus an explicit `bodyIndex++`), so only the odd-positioned body atoms
/// are examined; this is reproduced faithfully -- a missed guard merely demotes
/// the clause to the always-run unguarded list, so it is answer-neutral.
fn atomic_role_clause_guards(swapped: &DLClause) -> (Vec<AtomicConcept>, Vec<AtomicConcept>) {
    let mut guards1: Vec<AtomicConcept> = Vec::new();
    let mut guards2: Vec<AtomicConcept> = Vec::new();
    let delta = swapped.get_body_atom(0);
    let (Some(x), Some(y)) =
        (delta.get_argument_variable(0), delta.get_argument_variable(1))
    else {
        return (guards1, guards2);
    };
    let length = swapped.get_body_length();
    let mut body_index = 1;
    while body_index < length {
        let atom = swapped.get_body_atom(body_index);
        if let DLPredicate::AtomicConcept(concept) = atom.get_dl_predicate() {
            if let Some(variable) = atom.get_argument_variable(0) {
                if x == variable {
                    guards1.push(concept.clone());
                }
                if y == variable {
                    guards2.push(concept.clone());
                }
            }
        }
        // Java advances the index by two (loop step + inner `bodyIndex++`).
        body_index += 2;
    }
    (guards1, guards2)
}

/// All atomic concepts asserted on `node` in the committed extension (Java's
/// `m_binaryTableRetrieval` over `View.EXTENSION_THIS`, bound on the node column).
fn atomic_concepts_on_node_this(tableau: &Tableau, node: NodeId) -> Vec<AtomicConcept> {
    let retrieval = tableau.create_binary_retrieval(
        [-1, 1],
        [None, Some(TableauObject::Node(node))],
        View::ExtensionThis,
    );
    let mut concepts = Vec::new();
    for &tuple_index in &retrieval.tuple_indices {
        if let TableauObject::Concept(Concept::AtomicConcept(concept)) =
            tableau.binary_extension_table.get_tuple_object(tuple_index, 0)
        {
            concepts.push(concept.clone());
        }
    }
    concepts
}

pub struct HyperresolutionManager {
    /// `m_tupleConsumersByDeltaPredicate`: every clause indexed by its delta
    /// predicate (the unoptimized consumer list, most-recently-compiled first).
    evaluators_by_predicate: HashMap<DLPredicate, Vec<SharedEvaluator>>,
    /// `m_atomicRoleTupleConsumersUnguarded`: atomic-role clauses with no
    /// guarding atomic-concept body atom on either delta argument.
    unguarded_by_role: HashMap<AtomicRole, Vec<SharedEvaluator>>,
    /// `m_atomicRoleTupleConsumersByGuardConcept1`: atomic-role clauses indexed by
    /// an atomic concept guarding the delta's first argument.
    guarded_by_role_concept1: HashMap<AtomicRole, HashMap<AtomicConcept, Vec<SharedEvaluator>>>,
    /// `m_atomicRoleTupleConsumersByGuardConcept2`: indexed by a concept guarding
    /// the delta's second argument.
    guarded_by_role_concept2: HashMap<AtomicRole, HashMap<AtomicConcept, Vec<SharedEvaluator>>>,
}

impl HyperresolutionManager {
    /// Builds the manager with `AnywhereBlocking`'s all-true core-variable policy
    /// (the default / non-validated path, and the datalog engine).
    pub fn new(dl_clauses: &indexmap::IndexSet<DLClause>) -> HyperresolutionManager {
        Self::with_core_variable_policy(
            dl_clauses,
            crate::tableau::dl_clause_evaluator::CoreVariablePolicy::AllTrue,
        )
    }

    /// Builds the manager compiling each clause with the given core-variable
    /// policy (the validated/core blocking strategies use a different policy,
    /// affecting the `is_core` flag of derived unary facts).
    pub fn with_core_variable_policy(
        dl_clauses: &indexmap::IndexSet<DLClause>,
        core_variable_policy: crate::tableau::dl_clause_evaluator::CoreVariablePolicy,
    ) -> HyperresolutionManager {
        let clause_vec: Vec<DLClause> = dl_clauses.iter().cloned().collect();
        let values_buffer_manager =
            ValuesBufferManager::new(&clause_vec, &HashMap::new()).expect("buffer layout");

        // Index DL clauses by body (HyperresolutionManager.DLClauseBodyKey): every
        // clause with an identical body-atom sequence is compiled into a single
        // evaluator per delta atom. The first-seen clause of each group is the
        // representative body that drives body compilation and the core-variable
        // policy; the heads of all group members are derived together.
        let mut groups: Vec<(DLClause, Vec<DLClause>)> = Vec::new();
        let mut group_of_body: HashMap<Vec<Atom>, usize> = HashMap::new();
        for dl_clause in &clause_vec {
            let body = dl_clause.get_body_atoms();
            match group_of_body.get(&body) {
                Some(&index) => groups[index].1.push(dl_clause.clone()),
                None => {
                    group_of_body.insert(body, groups.len());
                    groups.push((dl_clause.clone(), vec![dl_clause.clone()]));
                }
            }
        }

        let mut evaluators_by_predicate: HashMap<DLPredicate, Vec<SharedEvaluator>> =
            HashMap::new();
        let mut unguarded_by_role: HashMap<AtomicRole, Vec<SharedEvaluator>> = HashMap::new();
        let mut guarded_by_role_concept1: HashMap<
            AtomicRole,
            HashMap<AtomicConcept, Vec<SharedEvaluator>>,
        > = HashMap::new();
        let mut guarded_by_role_concept2: HashMap<
            AtomicRole,
            HashMap<AtomicConcept, Vec<SharedEvaluator>>,
        > = HashMap::new();
        for (representative, members) in &groups {
            for body_atom_index in 0..representative.get_body_length() {
                let predicate = representative.get_body_atom(body_atom_index).get_dl_predicate();
                if is_predicate_with_extension(predicate) {
                    let swapped = swap_body_to_front(representative, body_atom_index);
                    let delta_atom = swapped.get_body_atom(0);
                    let delta_predicate = delta_atom.get_dl_predicate().clone();
                    let evaluator: SharedEvaluator =
                        Rc::new(RefCell::new(DLClauseEvaluator::compile(
                            &swapped,
                            members,
                            &values_buffer_manager,
                            core_variable_policy,
                        )));
                    evaluators_by_predicate
                        .entry(delta_predicate.clone())
                        .or_default()
                        .insert(0, Rc::clone(&evaluator));
                    // Guard-concept indexing (only for atomic-role deltas whose
                    // two arguments are both variables -- HermiT's constructor).
                    if let DLPredicate::AtomicRole(role) = &delta_predicate {
                        if delta_atom.get_argument(0).as_variable().is_some()
                            && delta_atom.get_argument(1).as_variable().is_some()
                        {
                            let (guards1, guards2) = atomic_role_clause_guards(&swapped);
                            if !guards1.is_empty() {
                                let map =
                                    guarded_by_role_concept1.entry(role.clone()).or_default();
                                for concept in &guards1 {
                                    map.entry(concept.clone())
                                        .or_default()
                                        .insert(0, Rc::clone(&evaluator));
                                }
                            }
                            if !guards2.is_empty() {
                                let map =
                                    guarded_by_role_concept2.entry(role.clone()).or_default();
                                for concept in &guards2 {
                                    map.entry(concept.clone())
                                        .or_default()
                                        .insert(0, Rc::clone(&evaluator));
                                }
                            }
                            if guards1.is_empty() && guards2.is_empty() {
                                unguarded_by_role
                                    .entry(role.clone())
                                    .or_default()
                                    .insert(0, Rc::clone(&evaluator));
                            }
                        }
                    }
                }
            }
        }
        HyperresolutionManager {
            evaluators_by_predicate,
            unguarded_by_role,
            guarded_by_role_concept1,
            guarded_by_role_concept2,
        }
    }

    /// Whether some clause has `owl:Thing` as its delta predicate -- HermiT's
    /// `m_tupleConsumersByDeltaPredicate.containsKey(AtomicConcept.THING)`, used to
    /// decide whether `owl:Thing` must be materialized on every node (so a
    /// `C(X) :- owl:Thing(X)` top-GCI fires).
    pub fn needs_thing_extension(&self) -> bool {
        self.evaluators_by_predicate.contains_key(&DLPredicate::AtomicConcept(
            crate::model::AtomicConcept::thing().clone(),
        ))
    }
    /// `containsKey(AtomicConcept.INTERNAL_NAMED)`.
    pub fn needs_named_extension(&self) -> bool {
        self.evaluators_by_predicate.contains_key(&DLPredicate::AtomicConcept(
            crate::model::AtomicConcept::internal_named().clone(),
        ))
    }
    /// `containsKey(InternalDatatype.RDFS_LITERAL)`.
    pub fn needs_rdfs_literal_extension(&self) -> bool {
        self.evaluators_by_predicate.contains_key(&DLPredicate::InternalDatatype(
            crate::model::InternalDatatype::rdfs_literal().clone(),
        ))
    }

    /// Applies the DL clauses to the current delta-old tuples.
    pub fn apply_dl_clauses(&mut self, tableau: &mut Tableau) {
        let binary_delta = snapshot_delta_old(tableau, 2);
        for (objects, dependency_set, is_core) in binary_delta {
            if tableau.contains_clash() {
                return;
            }
            self.apply_to_tuple(tableau, objects, dependency_set, is_core);
        }
        let ternary_delta = snapshot_delta_old(tableau, 3);
        for (objects, dependency_set, is_core) in ternary_delta {
            if tableau.contains_clash() {
                return;
            }
            self.apply_to_tuple(tableau, objects, dependency_set, is_core);
        }
    }

    fn apply_to_tuple(
        &mut self,
        tableau: &mut Tableau,
        objects: Vec<TableauObject>,
        dependency_set: PermanentDependencySet,
        is_core: bool,
    ) {
        let Some(predicate) = label_to_predicate(&objects[0]) else {
            return;
        };
        let Some(unoptimized) = self.evaluators_by_predicate.get(&predicate) else {
            return;
        };

        // Guard-concept optimization (HermiT `applyDLClauses`): for an atomic-role
        // delta tuple, when the number of clauses for the role exceeds the number
        // of positive atomic concepts on the two endpoints plus the unguarded
        // clause count, skip the full list and run only the unguarded clauses plus
        // those whose guarding concept is actually asserted on the endpoints.
        let mut apply_unoptimized = true;
        if let DLPredicate::AtomicRole(role) = &predicate {
            if let (Some(node1), Some(node2)) = (objects[1].as_node(), objects[2].as_node()) {
                let unguarded_count =
                    self.unguarded_by_role.get(role).map_or(0, |list| list.len());
                let positive1 = tableau.nodes[node1].get_number_of_positive_atomic_concepts();
                let positive2 = tableau.nodes[node2].get_number_of_positive_atomic_concepts();
                if (unoptimized.len() as i32) > positive1 + positive2 + unguarded_count as i32 {
                    apply_unoptimized = false;
                    // Unguarded clauses always fire.
                    let unguarded: Vec<SharedEvaluator> = self
                        .unguarded_by_role
                        .get(role)
                        .map(|list| list.iter().map(Rc::clone).collect())
                        .unwrap_or_default();
                    for evaluator in &unguarded {
                        evaluator.borrow_mut().set_delta_row(
                            objects.clone(),
                            dependency_set.clone(),
                            is_core,
                        );
                        evaluator.borrow_mut().evaluate(tableau);
                        if tableau.contains_clash() {
                            return;
                        }
                    }
                    // Clauses guarded by a concept on the delta's first argument.
                    if !tableau.contains_clash() {
                        let to_run = self.guarded_evaluators_for_node(
                            &self.guarded_by_role_concept1,
                            role,
                            tableau,
                            node1,
                        );
                        for evaluator in &to_run {
                            evaluator.borrow_mut().set_delta_row(
                                objects.clone(),
                                dependency_set.clone(),
                                is_core,
                            );
                            evaluator.borrow_mut().evaluate(tableau);
                            if tableau.contains_clash() {
                                return;
                            }
                        }
                    }
                    // Clauses guarded by a concept on the delta's second argument.
                    if !tableau.contains_clash() {
                        let to_run = self.guarded_evaluators_for_node(
                            &self.guarded_by_role_concept2,
                            role,
                            tableau,
                            node2,
                        );
                        for evaluator in &to_run {
                            evaluator.borrow_mut().set_delta_row(
                                objects.clone(),
                                dependency_set.clone(),
                                is_core,
                            );
                            evaluator.borrow_mut().evaluate(tableau);
                            if tableau.contains_clash() {
                                return;
                            }
                        }
                    }
                }
            }
        }

        if apply_unoptimized {
            let evaluators: Vec<SharedEvaluator> =
                unoptimized.iter().map(Rc::clone).collect();
            for evaluator in &evaluators {
                evaluator.borrow_mut().set_delta_row(
                    objects.clone(),
                    dependency_set.clone(),
                    is_core,
                );
                evaluator.borrow_mut().evaluate(tableau);
                if tableau.contains_clash() {
                    return;
                }
            }
        }
    }

    /// Collects, in guard-list order, the evaluators registered under any atomic
    /// concept actually asserted on `node` (Java walks the bound binary-table
    /// retrieval and runs the matching `compiledDLClauseInfos`).
    fn guarded_evaluators_for_node(
        &self,
        guarded_by_role_concept: &HashMap<AtomicRole, HashMap<AtomicConcept, Vec<SharedEvaluator>>>,
        role: &AtomicRole,
        tableau: &Tableau,
        node: NodeId,
    ) -> Vec<SharedEvaluator> {
        let mut to_run: Vec<SharedEvaluator> = Vec::new();
        if let Some(map) = guarded_by_role_concept.get(role) {
            for concept in atomic_concepts_on_node_this(tableau, node) {
                if let Some(list) = map.get(&concept) {
                    to_run.extend(list.iter().map(Rc::clone));
                }
            }
        }
        to_run
    }

    /// Runs the rule-application fixpoint, stopping at a clash or when no new
    /// facts are derived.
    pub fn saturate(&mut self, tableau: &mut Tableau) {
        loop {
            let changed = tableau.propagate_delta_new_all();
            if !changed {
                break;
            }
            self.apply_dl_clauses(tableau);
            if tableau.contains_clash() {
                break;
            }
        }
    }
}

fn snapshot_delta_old(
    tableau: &Tableau,
    arity: usize,
) -> Vec<(Vec<TableauObject>, PermanentDependencySet, bool)> {
    let table = if arity == 2 {
        &tableau.binary_extension_table
    } else {
        &tableau.ternary_extension_table
    };
    let (start, after_last) = table.view_range(View::DeltaOld);
    let empty = tableau.dependency_set_factory.empty_set();
    let mut result = Vec::new();
    'outer: for tuple_index in start..after_last {
        for column in 1..arity {
            let node = table.get_tuple_object(tuple_index, column).as_node().unwrap();
            if !tableau.nodes[node].is_active() {
                continue 'outer;
            }
        }
        let objects = (0..arity)
            .map(|c| table.get_tuple_object(tuple_index, c).clone())
            .collect();
        result.push((
            objects,
            table.get_dependency_set(tuple_index, &empty),
            table.is_core(tuple_index),
        ));
    }
    result
}
