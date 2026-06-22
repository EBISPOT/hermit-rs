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
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
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
    let mut bound_variables: HashSet<Variable> = HashSet::default();

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

/// Fills `concepts` (cleared first) with every atomic concept asserted on `node`
/// in the committed extension (Java's `m_binaryTableRetrieval` over
/// `View.EXTENSION_THIS`, bound on the node column). `index_scratch` is a reused
/// tuple-index buffer so the per-role-tuple guard probe allocates nothing:
/// `AtomicConcept` is a `Copy` `&'static` handle, so the collected concepts do
/// not borrow `tableau` and can be evaluated after the borrow is dropped.
fn atomic_concepts_on_node_this_into(
    tableau: &Tableau,
    node: NodeId,
    index_scratch: &mut Vec<usize>,
    concepts: &mut Vec<AtomicConcept>,
) {
    concepts.clear();
    index_scratch.clear();
    let table = &tableau.binary_extension_table;
    let binding_positions = [-1, 1];
    let bindings_buffer = [None, Some(TableauObject::Node(node))];
    // Mirror `create_binary_retrieval`'s selection (an indexed trie walk on the
    // bound node column, falling back to a view scan), but fill the reused index
    // buffer instead of allocating a fresh `Retrieval` per call. The bound column
    // is the node, which is always active here (it is one of the delta tuple's
    // endpoints), so the per-tuple activity/selection filter reduces to matching
    // the node binding -- already guaranteed by the index walk; for the scan
    // fallback we keep the explicit check.
    if table.indexed_tuple_indices_into(
        &binding_positions,
        &bindings_buffer,
        View::ExtensionThis,
        index_scratch,
    ) {
        for &tuple_index in index_scratch.iter() {
            let node_col = table.get_tuple_object(tuple_index, 1).as_node().unwrap();
            if !tableau.nodes[node_col].is_active() || node_col != node {
                continue;
            }
            if let TableauObject::Concept(Concept::AtomicConcept(concept)) =
                table.get_tuple_object(tuple_index, 0)
            {
                concepts.push(*concept);
            }
        }
    } else {
        let (start, after_last) = table.view_range(View::ExtensionThis);
        for tuple_index in start..after_last {
            let node_col = table.get_tuple_object(tuple_index, 1).as_node().unwrap();
            if !tableau.nodes[node_col].is_active() || node_col != node {
                continue;
            }
            if let TableauObject::Concept(Concept::AtomicConcept(concept)) =
                table.get_tuple_object(tuple_index, 0)
            {
                concepts.push(*concept);
            }
        }
    }
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
    /// Reused scratch buffers for the guard-concept path of `apply_to_tuple`, so
    /// the per-role-tuple endpoint-concept probe allocates nothing across the
    /// whole delta pass (both buffers hold `Copy`/`&'static` data, so they never
    /// borrow `tableau` and can be evaluated against `&mut tableau` afterwards).
    guard_index_scratch: Vec<usize>,
    guard_concept_scratch: Vec<AtomicConcept>,
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
            ValuesBufferManager::new(&clause_vec, &HashMap::default()).expect("buffer layout");

        // Index DL clauses by body (HyperresolutionManager.DLClauseBodyKey): every
        // clause with an identical body-atom sequence is compiled into a single
        // evaluator per delta atom. The first-seen clause of each group is the
        // representative body that drives body compilation and the core-variable
        // policy; the heads of all group members are derived together.
        let mut groups: Vec<(DLClause, Vec<DLClause>)> = Vec::new();
        let mut group_of_body: HashMap<Vec<Atom>, usize> = HashMap::default();
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
            HashMap::default();
        let mut unguarded_by_role: HashMap<AtomicRole, Vec<SharedEvaluator>> = HashMap::default();
        let mut guarded_by_role_concept1: HashMap<
            AtomicRole,
            HashMap<AtomicConcept, Vec<SharedEvaluator>>,
        > = HashMap::default();
        let mut guarded_by_role_concept2: HashMap<
            AtomicRole,
            HashMap<AtomicConcept, Vec<SharedEvaluator>>,
        > = HashMap::default();
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
            guard_index_scratch: Vec::new(),
            guard_concept_scratch: Vec::new(),
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
        // The DELTA_OLD ranges are fixed and append-only for the duration of this
        // pass (rule firing only adds DELTA_NEW tuples; a clash returns early), so
        // we snapshot just the eligible tuple *indices* up front -- preserving the
        // exact selection/activity semantics -- and read each tuple into one reused
        // buffer when we process it, instead of materialising a `Vec` per tuple
        // (Java HermiT reads the delta through a reused `Object[]`).
        let mut buf: Vec<TableauObject> = Vec::with_capacity(3);
        let binary_delta = snapshot_delta_old(tableau, 2);
        for (tuple_index, dependency_set) in binary_delta {
            if tableau.contains_clash() {
                return;
            }
            read_tuple_into(&tableau.binary_extension_table, tuple_index, 2, &mut buf);
            self.apply_to_tuple(tableau, &buf, dependency_set);
        }
        let ternary_delta = snapshot_delta_old(tableau, 3);
        for (tuple_index, dependency_set) in ternary_delta {
            if tableau.contains_clash() {
                return;
            }
            read_tuple_into(&tableau.ternary_extension_table, tuple_index, 3, &mut buf);
            self.apply_to_tuple(tableau, &buf, dependency_set);
        }
    }

    fn apply_to_tuple(
        &mut self,
        tableau: &mut Tableau,
        objects: &[TableauObject],
        dependency_set: PermanentDependencySet,
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
                    // Unguarded clauses always fire. Iterate in place (see the
                    // unoptimized branch below): `evaluate` never borrows `self`,
                    // so no `Vec`/`Rc::clone` snapshot of the list is needed.
                    if let Some(list) = self.unguarded_by_role.get(role) {
                        for evaluator in list {
                            evaluator.borrow_mut().evaluate(tableau, objects, &dependency_set);
                            if tableau.contains_clash() {
                                return;
                            }
                        }
                    }
                    // Borrow the two reused scratch buffers out of `self` for the
                    // duration of the guard probes. They hold `Copy`/`&'static`
                    // data only and are restored before returning, so iterating
                    // them while immutably borrowing `self.guarded_by_role_concept*`
                    // and mutably borrowing `tableau` (via `evaluate`) is sound and
                    // allocates nothing per role tuple.
                    let mut index_scratch = std::mem::take(&mut self.guard_index_scratch);
                    let mut concept_scratch = std::mem::take(&mut self.guard_concept_scratch);
                    // Clauses guarded by a concept on the delta's first argument.
                    // Evaluate in place (Java walks the bound retrieval and runs each
                    // matching consumer directly): `evaluate` borrows `tableau`, not
                    // `self`, so the guarded list can be iterated under the immutable
                    // `self` borrow — no `Vec`+`Rc::clone` snapshot of the matched
                    // evaluators per role tuple.
                    if !tableau.contains_clash() {
                        if let Some(map) = self.guarded_by_role_concept1.get(role) {
                            atomic_concepts_on_node_this_into(
                                tableau,
                                node1,
                                &mut index_scratch,
                                &mut concept_scratch,
                            );
                            for concept in &concept_scratch {
                                if let Some(list) = map.get(concept) {
                                    for evaluator in list {
                                        evaluator
                                            .borrow_mut()
                                            .evaluate(tableau, objects, &dependency_set);
                                        if tableau.contains_clash() {
                                            self.guard_index_scratch = index_scratch;
                                            self.guard_concept_scratch = concept_scratch;
                                            return;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // Clauses guarded by a concept on the delta's second argument.
                    if !tableau.contains_clash() {
                        if let Some(map) = self.guarded_by_role_concept2.get(role) {
                            atomic_concepts_on_node_this_into(
                                tableau,
                                node2,
                                &mut index_scratch,
                                &mut concept_scratch,
                            );
                            for concept in &concept_scratch {
                                if let Some(list) = map.get(concept) {
                                    for evaluator in list {
                                        evaluator
                                            .borrow_mut()
                                            .evaluate(tableau, objects, &dependency_set);
                                        if tableau.contains_clash() {
                                            self.guard_index_scratch = index_scratch;
                                            self.guard_concept_scratch = concept_scratch;
                                            return;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    self.guard_index_scratch = index_scratch;
                    self.guard_concept_scratch = concept_scratch;
                }
            }
        }

        if apply_unoptimized {
            // Iterate the clause list in place (Java runs
            // `m_compiledDLClauseInfos[i].evaluate(...)` directly). `evaluate`
            // borrows only `tableau` (a separate `&mut`) and the evaluator's own
            // `RefCell`; it never touches `self`, so holding the immutable borrow
            // of `unoptimized` across the loop is sound and avoids a per-delta
            // `Vec` alloc + an `Rc::clone` per clause.
            for evaluator in unoptimized {
                evaluator.borrow_mut().evaluate(tableau, objects, &dependency_set);
                if tableau.contains_clash() {
                    return;
                }
            }
        }
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

/// Reads `arity` objects of `tuple_index` from `table` into the reused `buf`
/// (cleared first). `TableauObject` is `Copy`, so this is a `memcpy`-style fill
/// with no allocation once `buf` has been sized -- mirroring Java's reused
/// `Object[]` tuple buffer.
fn read_tuple_into(
    table: &crate::tableau::extension_table::ExtensionTable,
    tuple_index: usize,
    arity: usize,
    buf: &mut Vec<TableauObject>,
) {
    buf.clear();
    for c in 0..arity {
        buf.push(*table.get_tuple_object(tuple_index, c));
    }
}

/// Snapshots the eligible DELTA_OLD tuple *indices* (with their dependency set
/// and core flag), captured up front with the same per-tuple node-activity check
/// as before. Storing indices rather than materialised object `Vec`s avoids a
/// per-tuple allocation; the caller reads each tuple into one reused buffer when
/// it processes it. The DELTA_OLD range is append-only for the pass, so the
/// indices stay valid (rule firing only appends DELTA_NEW tuples).
fn snapshot_delta_old(
    tableau: &Tableau,
    arity: usize,
) -> Vec<(usize, PermanentDependencySet)> {
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
        result.push((tuple_index, table.get_dependency_set(tuple_index, &empty)));
    }
    result
}
