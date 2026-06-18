// Port of org.semanticweb.HermiT.tableau.DLClauseEvaluator (the Worker VM and
// the ConjunctionCompiler / DLClauseCompiler that produces it).
//
// A DL clause body is compiled into a little program of `Worker` operations --
// a nested-loop join over the extension tables, with branch/jump control flow --
// that, on each full match, derives the head atom(s). The first body atom is
// the "delta" atom: its current tuple is set externally (by the hyperresolution
// loop) before `evaluate` is called.
//
// A retrieval is opened by collecting the matching tuple *indices* of its
// extension-table view (the trie walk / scan), then walked lazily: each
// `next()` reads the current tuple into the retrieval's reused buffer, mirroring
// Java's `Retrieval.open`/`next` over a shared tuple buffer rather than
// materialising every matching row up front.
//
// Disjunctive heads (`DeriveDisjunction`) drive the GroundDisjunction /
// disjunction-branching machinery (`tableau::branching`); Horn clauses
// (head length <= 1) derive their fact directly.
//
// The `is_core` flag of a derived unary head fact is set per the configured
// blocking strategy's `dlClauseBodyCompiled` (see `CoreVariablePolicy`):
// AnywhereBlocking / AncestorBlocking mark every variable core; the validated
// core strategies use a clause-dependent assignment, with a runtime
// `ComputeCoreVariables` worker for the single-head atomic-concept-inclusion
// case.
#![allow(dead_code)]

use std::cell::RefCell;
use rustc_hash::FxHashSet as HashSet;
use std::rc::Rc;

use crate::model::{Atom, DLClause, DLPredicate, Term, Variable};
use crate::tableau::dependency_set::{DependencySet, PermanentDependencySet};
use crate::tableau::extension_table::View;
use crate::tableau::hyperresolution::ValuesBufferManager;
use crate::tableau::node::NodeId;
use crate::tableau::node_type::NodeType;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;

/// How a derived unary head fact's `is_core` flag is computed, set by the
/// configured blocking strategy's `dlClauseBodyCompiled`:
/// - `AllTrue`: `AnywhereBlocking` / `AncestorBlocking` (every variable core).
/// - `SimpleCore`: `AnywhereValidatedBlocking` with `m_useSimpleCore` (no
///   variable core).
/// - `ComplexCore`: `AnywhereValidatedBlocking` without simple core (per-clause:
///   empty/single head -> none core, multi-head -> all core, and a single-head
///   atomic-concept-inclusion clause with >1 variable additionally runs the
///   `ComputeCoreVariables` worker to mark tree-deeper variables core).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CoreVariablePolicy {
    AllTrue,
    SimpleCore,
    ComplexCore,
}

impl CoreVariablePolicy {
    pub fn from_blocking_strategy_type(
        strategy: crate::configuration::BlockingStrategyType,
    ) -> CoreVariablePolicy {
        use crate::configuration::BlockingStrategyType;
        match strategy {
            BlockingStrategyType::SimpleCore => CoreVariablePolicy::SimpleCore,
            BlockingStrategyType::ComplexCore => CoreVariablePolicy::ComplexCore,
            // OPTIMAL resolves to AnywhereBlocking, never validated blocking.
            BlockingStrategyType::Optimal
            | BlockingStrategyType::Anywhere
            | BlockingStrategyType::Ancestor => CoreVariablePolicy::AllTrue,
        }
    }
}

// `Worker` is `Copy` so the VM can fetch the current op with a cheap register
// copy each step (Java executes `m_workers[pc]` in place); the two variants that
// carried `Vec`s keep them in side tables on the evaluator (`node_var_lists`,
// `disjunctions`) and hold only a `u32` index, which also shrinks the enum.
#[derive(Clone, Copy)]
enum Worker {
    CopyValues { from_retrieval: usize, from_column: usize, to_index: usize },
    CopyDependencySet { from_retrieval: usize, target_index: usize },
    BranchIfNotEqual { jump: i32, from_retrieval: usize, column1: usize, column2: usize },
    BranchIfNotNodeIdLessEqualThan { jump: i32, var1: usize, var2: usize },
    BranchIfNotNodeIdsAscendingOrEqual { jump: i32, node_vars: u32 },
    OpenRetrieval { retrieval: usize },
    NextRetrieval { retrieval: usize },
    HasMoreRetrieval { eof: i32, retrieval: usize },
    JumpTo { target: i32 },
    SetClash,
    DeriveUnaryFact { predicate: DLPredicate, argument_index: usize },
    DeriveBinaryFact { predicate: DLPredicate, argument1: usize, argument2: usize },
    DeriveTernaryFact { predicate: DLPredicate, argument1: usize, argument2: usize, argument3: usize },
    DeriveDisjunction { disjunction: u32 },
    /// `AnywhereValidatedBlocking.ComputeCoreVariables`: at runtime, mark every
    /// non-root tree variable strictly deeper than the shallowest mapped tree
    /// node as core. Only emitted for a complex-core single-head atomic-concept-
    /// inclusion clause with more than one variable.
    ComputeCoreVariables { variable_count: usize },
    /// `CallMatchStartedOnMonitor` / `CallMatchFinishedOnMonitor`: fire the
    /// `dlClauseMatchedStarted`/`dlClauseMatchedFinished` monitor events that
    /// bracket each head clause's derivation (`DLClauseEvaluator.compileHeads`).
    CallMatchStartedOnMonitor,
    CallMatchFinishedOnMonitor,
}

/// Side-table payload for a `DeriveDisjunction` worker (kept out of the `Copy`
/// `Worker` enum). Indexed by `Worker::DeriveDisjunction { disjunction }`.
struct DisjunctionWorker {
    head_predicates: Vec<DLPredicate>,
    copy_is_core: Vec<i32>,
    copy_values_to_arguments: Vec<usize>,
}

struct VmRetrieval {
    table_arity: usize,
    binding_positions: Vec<i32>,
    view: View,
    /// Matching tuple indices for the current open (reused across opens). Java's
    /// retrieval walks the tuple table lazily; we keep the matching indices and
    /// read the *current* tuple's objects into the reused `cur_objects` buffer on
    /// demand, instead of materialising a `RetrievalRow` (with an owned `Vec`) for
    /// every matching tuple up front. The dependency set is read straight from the
    /// table only when a full clause match needs it (`CopyDependencySet`), since
    /// most iterated tuples are filtered out by a join branch first.
    indices: Vec<usize>,
    position: usize,
    cur_objects: Vec<TableauObject>,
}

impl VmRetrieval {
    fn after_last(&self) -> bool {
        self.position >= self.indices.len()
    }

    #[inline]
    fn current_object(&self, column: usize) -> TableauObject {
        self.cur_objects[column]
    }

    /// The current tuple's dependency set, read on demand from the table.
    fn current_dependency_set(&self, tableau: &Tableau) -> PermanentDependencySet {
        let tuple_index = self.indices[self.position];
        let table = if self.table_arity == 2 {
            &tableau.binary_extension_table
        } else {
            &tableau.ternary_extension_table
        };
        table.get_dependency_set(tuple_index, &tableau.dependency_set_factory.empty_set())
    }

    /// Loads the current tuple's objects into the reused buffer (Java's `next()`
    /// reading into its shared tuple buffer). A no-op past the last tuple.
    fn load_current(&mut self, tableau: &Tableau) {
        if self.position >= self.indices.len() {
            return;
        }
        let tuple_index = self.indices[self.position];
        let arity = self.table_arity;
        let table = if arity == 2 {
            &tableau.binary_extension_table
        } else {
            &tableau.ternary_extension_table
        };
        self.cur_objects.clear();
        for c in 0..arity {
            self.cur_objects.push(*table.get_tuple_object(tuple_index, c));
        }
    }

    /// `next()`: advance to the next matching tuple and read it into the buffer.
    fn advance(&mut self, tableau: &Tableau) {
        self.position += 1;
        self.load_current(tableau);
    }
}

pub struct DLClauseEvaluator {
    workers: Vec<Worker>,
    /// Side tables for the `Vec`-carrying workers, keeping `Worker` `Copy`.
    node_var_lists: Vec<Vec<usize>>,
    disjunctions: Vec<DisjunctionWorker>,
    retrievals: Vec<VmRetrieval>,
    /// Shared with the `ValuesBufferManager` and every sibling evaluator (HermiT's
    /// single `m_valuesBuffer`); see `ValuesBufferManager::values_buffer`.
    values_buffer: Rc<RefCell<Vec<Option<TableauObject>>>>,
    core_variables: Vec<bool>,
    union_constituents: Vec<Option<PermanentDependencySet>>,
}

impl DLClauseEvaluator {
    /// Compiles a clause body (whose first atom is the delta atom) together with
    /// the list of head clauses sharing that body.
    pub fn compile(
        body_dl_clause: &DLClause,
        head_dl_clauses: &[DLClause],
        values_buffer_manager: &ValuesBufferManager,
        core_variable_policy: CoreVariablePolicy,
    ) -> DLClauseEvaluator {
        let body_atoms: Vec<Atom> = body_dl_clause.get_body_atoms();
        let head_variables = head_variables(head_dl_clauses);
        let mut compiler = Compiler::new(
            body_atoms,
            head_dl_clauses.to_vec(),
            body_dl_clause.clone(),
            core_variable_policy,
            head_variables,
            values_buffer_manager,
        );
        let first_atom_table_arity =
            body_dl_clause.get_body_atom(0).get_dl_predicate().arity() + 1;
        compiler.generate_code(first_atom_table_arity);
        let core_variables = compiler.initial_core_variables();
        let union_constituents = vec![None; compiler.retrievals.len()];
        DLClauseEvaluator {
            workers: compiler.workers,
            node_var_lists: compiler.node_var_lists,
            disjunctions: compiler.disjunctions,
            retrievals: compiler.retrievals,
            values_buffer: Rc::clone(&values_buffer_manager.values_buffer),
            core_variables,
            union_constituents,
        }
    }


    /// Runs the compiled clause over one delta tuple. The delta (the externally
    /// bound first body atom -- retrieval index 0) is read directly from the
    /// caller's `delta_objects`/`delta_dependency_set`, mirroring Java HermiT,
    /// whose evaluators read the delta-old retrieval's shared tuple buffer rather
    /// than each holding a private copy. This avoids copying the delta tuple (and
    /// cloning its dependency set) into every matching evaluator.
    pub fn evaluate(
        &mut self,
        tableau: &mut Tableau,
        delta_objects: &[TableauObject],
        delta_dependency_set: &PermanentDependencySet,
    ) {
        let mut program_counter: usize = 0;
        while program_counter < self.workers.len() && !tableau.contains_clash() {
            // Mirror DLClauseEvaluator.java:84: poll the interrupt flag on every
            // worker step so a long join can be cancelled promptly. note_interrupt()
            // is a no-op with the default -1 timeout; pending_interrupt is checked
            // to bail early so run_calculus can surface the latched Err.
            tableau.note_interrupt();
            if tableau.pending_interrupt.is_some() {
                return;
            }
            let worker = self.workers[program_counter];
            program_counter =
                self.execute(worker, program_counter, tableau, delta_objects, delta_dependency_set);
        }
    }

    /// Reads column `column` of `from_retrieval`'s current row -- the shared delta
    /// buffer for retrieval 0, else the join retrieval's current tuple.
    #[inline]
    fn retrieval_object(&self, from_retrieval: usize, column: usize, delta_objects: &[TableauObject]) -> TableauObject {
        if from_retrieval == 0 {
            delta_objects[column]
        } else {
            self.retrievals[from_retrieval].current_object(column)
        }
    }

    fn execute(
        &mut self,
        worker: Worker,
        program_counter: usize,
        tableau: &mut Tableau,
        delta_objects: &[TableauObject],
        delta_dependency_set: &PermanentDependencySet,
    ) -> usize {
        match worker {
            Worker::CopyValues { from_retrieval, from_column, to_index } => {
                let value = self.retrieval_object(from_retrieval, from_column, delta_objects);
                self.values_buffer.borrow_mut()[to_index] = Some(value);
                program_counter + 1
            }
            Worker::CopyDependencySet { from_retrieval, target_index } => {
                let dep = if from_retrieval == 0 {
                    delta_dependency_set.clone()
                } else {
                    self.retrievals[from_retrieval].current_dependency_set(tableau)
                };
                self.union_constituents[target_index] = Some(dep);
                program_counter + 1
            }
            Worker::BranchIfNotEqual { jump, from_retrieval, column1, column2 } => {
                let lhs = self.retrieval_object(from_retrieval, column1, delta_objects);
                let rhs = self.retrieval_object(from_retrieval, column2, delta_objects);
                if lhs == rhs {
                    program_counter + 1
                } else {
                    jump as usize
                }
            }
            Worker::BranchIfNotNodeIdLessEqualThan { jump, var1, var2 } => {
                let id1 = self.node_id_at(var1, tableau);
                let id2 = self.node_id_at(var2, tableau);
                if id1 <= id2 {
                    program_counter + 1
                } else {
                    jump as usize
                }
            }
            Worker::BranchIfNotNodeIdsAscendingOrEqual { jump, node_vars } => {
                let node_vars = &self.node_var_lists[node_vars as usize];
                let mut strictly_ascending = true;
                let mut all_equal = true;
                let mut last_id = self.node_id_at(node_vars[0], tableau);
                for &var in &node_vars[1..] {
                    let id = self.node_id_at(var, tableau);
                    if last_id >= id {
                        strictly_ascending = false;
                    }
                    if id != last_id {
                        all_equal = false;
                    }
                    last_id = id;
                }
                if (!strictly_ascending && all_equal) || (strictly_ascending && !all_equal) {
                    program_counter + 1
                } else {
                    jump as usize
                }
            }
            Worker::OpenRetrieval { retrieval } => {
                let vb = Rc::clone(&self.values_buffer);
                let vb_ref = vb.borrow();
                open_retrieval(&mut self.retrievals[retrieval], &vb_ref, tableau);
                program_counter + 1
            }
            Worker::NextRetrieval { retrieval } => {
                self.retrievals[retrieval].advance(tableau);
                program_counter + 1
            }
            Worker::HasMoreRetrieval { eof, retrieval } => {
                if self.retrievals[retrieval].after_last() {
                    eof as usize
                } else {
                    program_counter + 1
                }
            }
            Worker::JumpTo { target } => target as usize,
            Worker::CallMatchStartedOnMonitor => {
                tableau.monitor_event(|m| m.dl_clause_matched_started());
                program_counter + 1
            }
            Worker::CallMatchFinishedOnMonitor => {
                tableau.monitor_event(|m| m.dl_clause_matched_finished());
                program_counter + 1
            }
            Worker::SetClash => {
                let dependency_set = self.union_dependency_set(&mut tableau.dependency_set_factory);
                tableau.set_clash(&dependency_set);
                program_counter + 1
            }
            Worker::DeriveUnaryFact { predicate, argument_index } => {
                let node = self.node_at(argument_index);
                let is_core = self.core_variables[argument_index];
                let dependency_set = self.union_dependency_set(&mut tableau.dependency_set_factory);
                tableau.add_unary_from_predicate(predicate, node, &dependency_set, is_core);
                program_counter + 1
            }
            Worker::DeriveBinaryFact { predicate, argument1, argument2 } => {
                let node1 = self.node_at(argument1);
                let node2 = self.node_at(argument2);
                let dependency_set = self.union_dependency_set(&mut tableau.dependency_set_factory);
                tableau.add_binary_from_predicate(predicate, node1, node2, &dependency_set, true);
                program_counter + 1
            }
            Worker::DeriveTernaryFact { predicate, argument1, argument2, argument3 } => {
                let node1 = self.node_at(argument1);
                let node2 = self.node_at(argument2);
                let node3 = self.node_at(argument3);
                let dependency_set = self.union_dependency_set(&mut tableau.dependency_set_factory);
                tableau.add_ternary_from_predicate(
                    predicate,
                    node1,
                    node2,
                    node3,
                    &dependency_set,
                    true,
                );
                program_counter + 1
            }
            Worker::DeriveDisjunction { disjunction } => {
                let d = &self.disjunctions[disjunction as usize];
                let arguments: Vec<NodeId> = d
                    .copy_values_to_arguments
                    .iter()
                    .map(|&i| self.node_at(i))
                    .collect();
                let is_core: Vec<bool> = d
                    .copy_is_core
                    .iter()
                    .map(|&c| if c == -1 { true } else { self.core_variables[c as usize] })
                    .collect();
                let head_predicates = d.head_predicates.clone();
                let dependency_set = self.union_dependency_set(&mut tableau.dependency_set_factory);
                tableau.derive_disjunction(head_predicates, arguments, is_core, dependency_set);
                program_counter + 1
            }
            Worker::ComputeCoreVariables { variable_count } => {
                // The root of the subtree induced by the mapped nodes is the
                // shallowest tree node; everything strictly below it cannot be core.
                let mut potential_non_core: Option<NodeId> = None;
                for variable_index in (0..variable_count).rev() {
                    let Some(node) = self.values_buffer.borrow()[variable_index]
                        .as_ref()
                        .and_then(|o| o.as_node())
                    else {
                        continue;
                    };
                    let is_shallower = match potential_non_core {
                        None => true,
                        Some(current) => {
                            tableau.nodes[node].get_tree_depth()
                                < tableau.nodes[current].get_tree_depth()
                        }
                    };
                    if tableau.nodes[node].get_node_type() == NodeType::TreeNode && is_shallower {
                        potential_non_core = Some(node);
                    }
                }
                if let Some(potential_non_core) = potential_non_core {
                    let root_depth = tableau.nodes[potential_non_core].get_tree_depth();
                    for variable_index in (0..variable_count).rev() {
                        let Some(node) = self.values_buffer.borrow()[variable_index]
                            .as_ref()
                            .and_then(|o| o.as_node())
                        else {
                            continue;
                        };
                        if !tableau.nodes[node].is_root_node()
                            && potential_non_core != node
                            && root_depth < tableau.nodes[node].get_tree_depth()
                        {
                            self.core_variables[variable_index] = true;
                        }
                    }
                }
                program_counter + 1
            }
        }
    }

    fn node_at(&self, variable_index: usize) -> NodeId {
        self.values_buffer.borrow()[variable_index]
            .as_ref()
            .and_then(|o| o.as_node())
            .expect("variable bound to a node")
    }
    fn node_id_at(&self, variable_index: usize, tableau: &Tableau) -> i32 {
        tableau.nodes[self.node_at(variable_index)].get_node_id()
    }
    /// The derived fact's dependency set: the interned permanent union of the
    /// copied body-atom constituents. Built directly (no throwaway
    /// `UnionDependencySet`), and returned as a `Permanent` so the consuming
    /// `get_permanent` takes its fast path.
    fn union_dependency_set(
        &self,
        factory: &mut crate::tableau::dependency_set::DependencySetFactory,
    ) -> DependencySet {
        DependencySet::Permanent(factory.permanent_union_of(&self.union_constituents))
    }
}

/// `open()`: collect the matching tuple indices for this retrieval into its
/// reused `indices` buffer and load the first one. The tuples themselves are read
/// lazily (one at a time, on `advance`) into the retrieval's reused buffer rather
/// than materialised up front, mirroring Java's `Retrieval.open`/`next`.
fn open_retrieval(
    retrieval: &mut VmRetrieval,
    values_buffer: &[Option<TableauObject>],
    tableau: &Tableau,
) {
    let arity = retrieval.table_arity;
    let table = if arity == 2 {
        &tableau.binary_extension_table
    } else {
        &tableau.ternary_extension_table
    };
    let (start, after_last) = table.view_range(retrieval.view);
    retrieval.indices.clear();
    retrieval.position = 0;
    let keep = |tuple_index: usize| -> bool {
        for column in 1..arity {
            let node = table.get_tuple_object(tuple_index, column).as_node().unwrap();
            if !tableau.nodes[node].is_active() {
                return false;
            }
        }
        for column in 0..arity {
            let binding_position = retrieval.binding_positions[column];
            if binding_position != -1 {
                let stored = table.get_tuple_object(tuple_index, column);
                match &values_buffer[binding_position as usize] {
                    Some(expected) if stored == expected => {}
                    _ => return false,
                }
            }
        }
        true
    };
    // Mirror ExtensionTableWithTupleIndexes.createRetrieval: an IndexedRetrieval
    // (trie walk, reverse-insertion DFS order over the unbound suffix columns)
    // when a leading column is bound, else an ascending UnindexedRetrieval scan
    // over the view window. A plain ascending-scan-then-reverse only coincides
    // with the trie order when the unbound suffix is a single column, so it must
    // not be used for ternary joins with two free node columns.
    if table.indexed_tuple_indices_into(
        &retrieval.binding_positions,
        values_buffer,
        retrieval.view,
        &mut retrieval.indices,
    ) {
        // Indexed: the buffer was filled with the view-windowed matches; drop the
        // ones whose nodes are inactive or whose non-prefix bindings disagree.
        retrieval.indices.retain(|&t| keep(t));
    } else {
        // No usable index: scan the view window, filtering as we go.
        retrieval.indices.extend((start..after_last).filter(|&t| keep(t)));
    }
    retrieval.load_current(tableau);
}

fn head_variables(head_dl_clauses: &[DLClause]) -> Vec<Variable> {
    let mut result: Vec<Variable> = Vec::new();
    for dl_clause in head_dl_clauses {
        for head_index in 0..dl_clause.get_head_length() {
            let atom = dl_clause.get_head_atom(head_index);
            for argument_index in 0..atom.get_arity() {
                if let Some(variable) = atom.get_argument_variable(argument_index) {
                    if !result.contains(variable) {
                        result.push(variable.clone());
                    }
                }
            }
        }
    }
    result
}

// ---------------------------------------------------------------------------
// The compiler (ConjunctionCompiler + DLClauseCompiler).
// ---------------------------------------------------------------------------

struct Compiler<'a> {
    body_atoms: Vec<Atom>,
    head_dl_clauses: Vec<DLClause>,
    /// The body (delta-reordered) clause, used by the blocking strategy's
    /// `dlClauseBodyCompiled` to read `getHeadLength` / `isAtomicConceptInclusion`.
    body_dl_clause: DLClause,
    policy: CoreVariablePolicy,
    variables: Vec<Variable>,
    bound_so_far: HashSet<Variable>,
    workers: Vec<Worker>,
    node_var_lists: Vec<Vec<usize>>,
    disjunctions: Vec<DisjunctionWorker>,
    retrievals: Vec<VmRetrieval>,
    labels: Vec<Option<usize>>,
    values_buffer_manager: &'a ValuesBufferManager,
}

impl<'a> Compiler<'a> {
    fn new(
        body_atoms: Vec<Atom>,
        head_dl_clauses: Vec<DLClause>,
        body_dl_clause: DLClause,
        policy: CoreVariablePolicy,
        head_variables: Vec<Variable>,
        values_buffer_manager: &'a ValuesBufferManager,
    ) -> Compiler<'a> {
        // The body variables that occur again in a later body atom, then the
        // head variables (mirroring ConjunctionCompiler's constructor).
        let mut variables: Vec<Variable> = Vec::new();
        for body_index in 0..body_atoms.len() {
            let atom = &body_atoms[body_index];
            for argument_index in 0..atom.get_arity() {
                if let Some(variable) = atom.get_argument_variable(argument_index) {
                    if !variables.contains(variable)
                        && occurs_in_body_atoms_after(&body_atoms, variable, body_index + 1)
                    {
                        variables.push(variable.clone());
                    }
                }
            }
        }
        for variable in head_variables {
            if !variables.contains(&variable) {
                variables.push(variable);
            }
        }
        Compiler {
            body_atoms,
            head_dl_clauses,
            body_dl_clause,
            policy,
            variables,
            bound_so_far: HashSet::default(),
            workers: Vec::new(),
            node_var_lists: Vec::new(),
            disjunctions: Vec::new(),
            retrievals: Vec::new(),
            labels: Vec::new(),
            values_buffer_manager,
        }
    }

    /// Whether the complex-core policy adds the runtime `ComputeCoreVariables`
    /// worker for this clause: a single-head atomic-concept inclusion with more
    /// than one variable (`AnywhereValidatedBlocking.dlClauseBodyCompiled`).
    fn complex_core_uses_worker(&self) -> bool {
        self.body_dl_clause.get_head_length() == 1
            && self.body_dl_clause.is_atomic_concept_inclusion()
            && self.variables.len() > 1
    }

    /// The compile-time initial `core_variables`, per the blocking strategy's
    /// `dlClauseBodyCompiled` (the `ComputeCoreVariables` worker refines the
    /// complex-core single-head case further at runtime).
    fn initial_core_variables(&self) -> Vec<bool> {
        let count = self.variables.len();
        match self.policy {
            CoreVariablePolicy::AllTrue => vec![true; count],
            CoreVariablePolicy::SimpleCore => vec![false; count],
            CoreVariablePolicy::ComplexCore => {
                // headLength 0 or 1 -> none core (the worker handles the single-head
                // atomic-concept-inclusion case); headLength > 1 -> all core.
                if self.body_dl_clause.get_head_length() > 1 {
                    vec![true; count]
                } else {
                    vec![false; count]
                }
            }
        }
    }

    fn index_of(&self, variable: &Variable) -> i32 {
        self.variables
            .iter()
            .position(|v| v == variable)
            .map(|i| i as i32)
            .unwrap_or(-1)
    }

    fn add_label(&mut self) -> i32 {
        let label_index = self.labels.len();
        self.labels.push(None);
        -(label_index as i32)
    }
    fn set_label_program_counter(&mut self, label_id: i32) {
        self.labels[(-label_id) as usize] = Some(self.workers.len());
    }

    fn generate_code(&mut self, first_atom_table_arity: usize) {
        self.labels.push(None); // m_labels.add(null)
        self.retrievals.push(VmRetrieval {
            table_arity: first_atom_table_arity,
            binding_positions: vec![-1; first_atom_table_arity],
            view: View::DeltaOld,
            indices: Vec::new(),
            position: 0,
            cur_objects: Vec::new(),
        });
        let after_rule = self.add_label();
        let first_atom = self.body_atoms[0].clone();
        self.compile_check_unbound_variable_matches(&first_atom, 0, after_rule);
        self.compile_generate_bindings(0, &first_atom);
        self.workers.push(Worker::CopyDependencySet { from_retrieval: 0, target_index: 0 });
        self.compile_body_atom(1, after_rule);
        self.set_label_program_counter(after_rule);
        self.resolve_labels();
    }

    fn compile_body_atom(&mut self, body_atom_index: usize, last_atom_next_element: i32) {
        if body_atom_index == self.body_atoms.len() {
            self.compile_heads();
            return;
        }
        let atom = self.body_atoms[body_atom_index].clone();
        let predicate = atom.get_dl_predicate().clone();
        if matches!(predicate, DLPredicate::NodeIdLessEqualThan) {
            let var1 = self.index_of(atom.get_argument_variable(0).unwrap()) as usize;
            let var2 = self.index_of(atom.get_argument_variable(1).unwrap()) as usize;
            self.workers.push(Worker::BranchIfNotNodeIdLessEqualThan {
                jump: last_atom_next_element,
                var1,
                var2,
            });
            self.compile_body_atom(body_atom_index + 1, last_atom_next_element);
        } else if matches!(predicate, DLPredicate::NodeIDsAscendingOrEqual(_)) {
            let node_vars: Vec<usize> = (0..atom.get_arity())
                .map(|i| self.index_of(atom.get_argument_variable(i).unwrap()) as usize)
                .collect();
            let node_vars_index = self.node_var_lists.len() as u32;
            self.node_var_lists.push(node_vars);
            self.workers.push(Worker::BranchIfNotNodeIdsAscendingOrEqual {
                jump: last_atom_next_element,
                node_vars: node_vars_index,
            });
            self.compile_body_atom(body_atom_index + 1, last_atom_next_element);
        } else {
            let after_loop = self.add_label();
            let next_element = self.add_label();
            let arity = atom.get_arity();
            let mut binding_positions = vec![0i32; arity + 1];
            binding_positions[0] = self
                .values_buffer_manager
                .body_dl_predicates_to_indexes[&predicate] as i32;
            for argument_index in 0..arity {
                let term = atom.get_argument(argument_index);
                match term {
                    Term::Variable(variable) => {
                        if self.bound_so_far.contains(variable) {
                            binding_positions[argument_index + 1] = self.index_of(variable);
                        } else {
                            binding_positions[argument_index + 1] = -1;
                        }
                    }
                    other => {
                        binding_positions[argument_index + 1] = self
                            .values_buffer_manager
                            .body_nonvariable_terms_to_indexes[other]
                            as i32;
                    }
                }
            }
            self.retrievals.push(VmRetrieval {
                table_arity: arity + 1,
                binding_positions,
                view: View::ExtensionThis,
                indices: Vec::new(),
                position: 0,
                cur_objects: Vec::new(),
            });
            let retrieval_index = self.retrievals.len() - 1;
            self.workers.push(Worker::OpenRetrieval { retrieval: retrieval_index });
            let loop_start = self.workers.len() as i32;
            self.workers
                .push(Worker::HasMoreRetrieval { eof: after_loop, retrieval: retrieval_index });
            self.compile_check_unbound_variable_matches(&atom, retrieval_index, next_element);
            self.compile_generate_bindings(retrieval_index, &atom);
            self.workers.push(Worker::CopyDependencySet {
                from_retrieval: retrieval_index,
                target_index: retrieval_index,
            });
            self.compile_body_atom(body_atom_index + 1, next_element);
            self.set_label_program_counter(next_element);
            self.workers.push(Worker::NextRetrieval { retrieval: retrieval_index });
            self.workers.push(Worker::JumpTo { target: loop_start });
            self.set_label_program_counter(after_loop);
        }
    }

    fn compile_check_unbound_variable_matches(
        &mut self,
        atom: &Atom,
        retrieval_index: usize,
        jump: i32,
    ) {
        for outer in 0..atom.get_arity() {
            if let Some(variable) = atom.get_argument_variable(outer) {
                let variable = variable.clone();
                if !self.bound_so_far.contains(&variable) {
                    for inner in (outer + 1)..atom.get_arity() {
                        if matches!(atom.get_argument(inner), Term::Variable(v) if *v == variable) {
                            self.workers.push(Worker::BranchIfNotEqual {
                                jump,
                                from_retrieval: retrieval_index,
                                column1: outer + 1,
                                column2: inner + 1,
                            });
                        }
                    }
                }
            }
        }
    }

    fn compile_generate_bindings(&mut self, retrieval_index: usize, atom: &Atom) {
        for argument_index in 0..atom.get_arity() {
            if let Some(variable) = atom.get_argument_variable(argument_index) {
                let variable = variable.clone();
                if !self.bound_so_far.contains(&variable) {
                    let variable_index = self.index_of(&variable);
                    if variable_index != -1 {
                        self.workers.push(Worker::CopyValues {
                            from_retrieval: retrieval_index,
                            from_column: argument_index + 1,
                            to_index: variable_index as usize,
                        });
                        self.bound_so_far.insert(variable);
                    }
                }
            }
        }
    }

    fn compile_heads(&mut self) {
        // `dlClauseBodyCompiled` runs before the head derivations. For the
        // complex-core single-head atomic-concept-inclusion case it appends the
        // `ComputeCoreVariables` worker, which refines `core_variables` at runtime
        // from the bound nodes' tree depths.
        if self.policy == CoreVariablePolicy::ComplexCore && self.complex_core_uses_worker() {
            self.workers.push(Worker::ComputeCoreVariables {
                variable_count: self.variables.len(),
            });
        }
        let head_clauses = self.head_dl_clauses.clone();
        for head_clause in &head_clauses {
            // `compileHeads` brackets each head clause's derivation with the
            // dlClauseMatched monitor events (the monitor is always present here).
            self.workers.push(Worker::CallMatchStartedOnMonitor);
            let head_length = head_clause.get_head_length();
            if head_length == 0 {
                self.workers.push(Worker::SetClash);
            } else if head_length == 1 {
                let atom = head_clause.get_head_atom(0);
                let predicate = atom.get_dl_predicate().clone();
                match atom.get_arity() {
                    1 => {
                        let argument_index =
                            self.index_of(atom.get_argument_variable(0).unwrap()) as usize;
                        self.workers
                            .push(Worker::DeriveUnaryFact { predicate, argument_index });
                    }
                    2 => {
                        let argument1 =
                            self.index_of(atom.get_argument_variable(0).unwrap()) as usize;
                        let argument2 =
                            self.index_of(atom.get_argument_variable(1).unwrap()) as usize;
                        self.workers.push(Worker::DeriveBinaryFact {
                            predicate,
                            argument1,
                            argument2,
                        });
                    }
                    3 => {
                        let argument1 =
                            self.index_of(atom.get_argument_variable(0).unwrap()) as usize;
                        let argument2 =
                            self.index_of(atom.get_argument_variable(1).unwrap()) as usize;
                        let argument3 =
                            self.index_of(atom.get_argument_variable(2).unwrap()) as usize;
                        self.workers.push(Worker::DeriveTernaryFact {
                            predicate,
                            argument1,
                            argument2,
                            argument3,
                        });
                    }
                    _ => panic!("Unsupported atom arity."),
                }
            } else {
                let mut head_predicates = Vec::with_capacity(head_length);
                let mut copy_is_core = Vec::with_capacity(head_length);
                let mut copy_values_to_arguments = Vec::new();
                for head_index in 0..head_length {
                    let atom = head_clause.get_head_atom(head_index);
                    let predicate = atom.get_dl_predicate().clone();
                    for argument_index in 0..atom.get_arity() {
                        let variable_index =
                            self.index_of(atom.get_argument_variable(argument_index).unwrap());
                        copy_values_to_arguments.push(variable_index as usize);
                    }
                    if predicate.arity() == 1 {
                        copy_is_core.push(self.index_of(atom.get_argument_variable(0).unwrap()));
                    } else {
                        copy_is_core.push(-1);
                    }
                    head_predicates.push(predicate);
                }
                let disjunction_index = self.disjunctions.len() as u32;
                self.disjunctions.push(DisjunctionWorker {
                    head_predicates,
                    copy_is_core,
                    copy_values_to_arguments,
                });
                self.workers.push(Worker::DeriveDisjunction { disjunction: disjunction_index });
            }
            self.workers.push(Worker::CallMatchFinishedOnMonitor);
        }
    }

    fn resolve_labels(&mut self) {
        for worker in &mut self.workers {
            let jump = match worker {
                Worker::BranchIfNotEqual { jump, .. }
                | Worker::BranchIfNotNodeIdLessEqualThan { jump, .. }
                | Worker::BranchIfNotNodeIdsAscendingOrEqual { jump, .. }
                | Worker::HasMoreRetrieval { eof: jump, .. }
                | Worker::JumpTo { target: jump } => Some(jump),
                _ => None,
            };
            if let Some(jump) = jump {
                if *jump < 0 {
                    *jump = self.labels[(-*jump) as usize]
                        .expect("label resolved") as i32;
                }
            }
        }
    }
}

fn occurs_in_body_atoms_after(body_atoms: &[Atom], variable: &Variable, start_index: usize) -> bool {
    body_atoms[start_index..]
        .iter()
        .any(|atom| atom.contains_variable(variable))
}

#[cfg(test)]
mod core_variable_policy_tests {
    use super::CoreVariablePolicy;
    use crate::configuration::BlockingStrategyType;

    // The validated/core blocking strategies must drive a non-all-true core
    // policy (SimpleCore -> none core, ComplexCore -> by head length), while the
    // anywhere/ancestor strategies (and OPTIMAL, which resolves to anywhere) mark
    // every variable core. End-to-end answer parity across all of these is
    // covered by tests/blocking_strategy_tests.rs.
    #[test]
    fn policy_follows_blocking_strategy() {
        assert_eq!(
            CoreVariablePolicy::from_blocking_strategy_type(BlockingStrategyType::SimpleCore),
            CoreVariablePolicy::SimpleCore
        );
        assert_eq!(
            CoreVariablePolicy::from_blocking_strategy_type(BlockingStrategyType::ComplexCore),
            CoreVariablePolicy::ComplexCore
        );
        for strategy in [
            BlockingStrategyType::Optimal,
            BlockingStrategyType::Anywhere,
            BlockingStrategyType::Ancestor,
        ] {
            assert_eq!(
                CoreVariablePolicy::from_blocking_strategy_type(strategy),
                CoreVariablePolicy::AllTrue
            );
        }
    }
}
