// Port of org.semanticweb.HermiT.tableau.{ExtensionTable, ExtensionTableWithTupleIndexes}
// -- the storage half (the parts that do not touch the node arena).
//
// An extension table keeps the ABox assertions during a tableau run: a binary
// (concept, node) table and a ternary (predicate, node, node) table. Tuples are
// appended; backtracking truncates the table back to a saved index. The tables
// are indexed by tries (`TupleIndex`) for fast lookup.
//
// HermiT keeps the per-tuple dependency set as an extra tuple column and the
// "core" flag in a bitset; this port keeps them in parallel vectors indexed by
// tuple index. The `postAdd` / `postRemove` side effects on nodes, and the
// activity checks (which need the node arena), live on `Tableau`; the methods
// here are pure storage.
#![allow(dead_code)]

use crate::tableau::dependency_set::{DependencySetFactory, PermanentDependencySet};
use crate::tableau::object::TableauObject;
use crate::tableau::tuple_index::{TupleIndex, TupleIndexRetrieval};
use crate::tableau::tuple_table::TupleTable;

/// The portion of the table a retrieval ranges over.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum View {
    ExtensionThis,
    ExtensionOld,
    DeltaOld,
    Total,
}

/// The outcome of attempting to store a tuple.
pub enum StoreOutcome {
    Added(usize),
    AlreadyPresent(usize),
}

pub struct ExtensionTable {
    arity: usize,
    tuple_table: TupleTable<TableauObject>,
    needs_dependency_sets: bool,
    tuple_indexes: Vec<TupleIndex<TableauObject>>,
    dependency_sets: Vec<Option<PermanentDependencySet>>,
    core_flags: Vec<bool>,
    is_real_core: bool,
    after_extension_old: usize,
    after_extension_this: usize,
    after_delta_new: usize,
    indices_by_branching_point: Vec<usize>,
}

impl ExtensionTable {
    pub fn new(
        arity: usize,
        needs_dependency_sets: bool,
        indexing_sequences: Vec<Vec<usize>>,
        is_real_core: bool,
    ) -> ExtensionTable {
        ExtensionTable {
            arity,
            tuple_table: TupleTable::new(arity),
            needs_dependency_sets,
            tuple_indexes: indexing_sequences.into_iter().map(TupleIndex::new).collect(),
            dependency_sets: Vec::new(),
            core_flags: Vec::new(),
            is_real_core,
            after_extension_old: 0,
            after_extension_this: 0,
            after_delta_new: 0,
            indices_by_branching_point: vec![0; 2 * 3],
        }
    }

    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn get_tuple_object(&self, tuple_index: usize, object_index: usize) -> &TableauObject {
        self.tuple_table
            .get_tuple_object(tuple_index, object_index)
            .expect("tuple slot occupied")
    }

    pub fn get_dependency_set(
        &self,
        tuple_index: usize,
        empty_set: &PermanentDependencySet,
    ) -> PermanentDependencySet {
        if self.needs_dependency_sets {
            self.dependency_sets
                .get(tuple_index)
                .and_then(|d| d.clone())
                .unwrap_or_else(|| empty_set.clone())
        } else {
            empty_set.clone()
        }
    }

    pub fn is_core(&self, tuple_index: usize) -> bool {
        if self.is_real_core {
            self.core_flags.get(tuple_index).copied().unwrap_or(false)
        } else {
            true
        }
    }

    fn add_core(&mut self, tuple_index: usize) {
        if self.is_real_core {
            if tuple_index >= self.core_flags.len() {
                self.core_flags.resize(tuple_index + 1, false);
            }
            self.core_flags[tuple_index] = true;
        }
    }

    /// Returns the tuple index of `tuple` via the primary index, or -1.
    pub fn get_tuple_index(&self, tuple: &[TableauObject]) -> i32 {
        self.tuple_indexes[0].get_tuple_index(tuple)
    }

    /// Stores `tuple` if not already present. The caller is responsible for the
    /// activity / owl:Thing / rdfs:Literal filtering (which needs the arena and
    /// the tableau flags) before calling.
    pub fn store_tuple(
        &mut self,
        tuple: &[TableauObject],
        dependency_set: PermanentDependencySet,
        is_core: bool,
        factory: &mut DependencySetFactory,
    ) -> StoreOutcome {
        let first_free = self.tuple_table.get_first_free_tuple_index();
        let add_index = self.tuple_indexes[0].add_tuple(tuple, first_free as i32);
        if add_index == first_free as i32 {
            for index in &mut self.tuple_indexes[1..] {
                index.add_tuple(tuple, add_index);
            }
            self.tuple_table.add_tuple(tuple);
            let idx = add_index as usize;
            if self.needs_dependency_sets {
                factory.add_usage(&dependency_set);
                if idx >= self.dependency_sets.len() {
                    self.dependency_sets.resize(idx + 1, None);
                }
                self.dependency_sets[idx] = Some(dependency_set);
            }
            if self.is_real_core {
                if idx >= self.core_flags.len() {
                    self.core_flags.resize(idx + 1, false);
                }
                self.core_flags[idx] = is_core;
            }
            self.after_delta_new = self.tuple_table.get_first_free_tuple_index();
            StoreOutcome::Added(idx)
        } else {
            StoreOutcome::AlreadyPresent(add_index as usize)
        }
    }

    /// Upgrades an already-present tuple to core, returning whether it changed.
    pub fn upgrade_core(&mut self, tuple_index: usize, is_core: bool) -> bool {
        if is_core && !self.is_core(tuple_index) {
            self.add_core(tuple_index);
            true
        } else {
            false
        }
    }

    pub fn propagate_delta_new(&mut self) -> bool {
        let delta_new_not_empty = self.after_extension_this != self.after_delta_new;
        self.after_extension_old = self.after_extension_this;
        self.after_extension_this = self.after_delta_new;
        self.after_delta_new = self.tuple_table.get_first_free_tuple_index();
        delta_new_not_empty
    }

    pub fn branching_point_pushed(&mut self, level: usize) {
        let start = level * 3;
        let required = start + 3;
        if required > self.indices_by_branching_point.len() {
            self.indices_by_branching_point.resize(required, 0);
        }
        self.indices_by_branching_point[start] = self.after_extension_old;
        self.indices_by_branching_point[start + 1] = self.after_extension_this;
        self.indices_by_branching_point[start + 2] = self.after_delta_new;
    }

    /// Backtracks to the given branching-point level, returning the removed
    /// tuples (most-recent first), each paired with its stored core flag, so the
    /// caller can run `postRemove` with the correct `isCore` (HermiT passes the
    /// tuple's core status to `assertionRemoved`).
    pub fn backtrack(
        &mut self,
        level: usize,
        factory: &mut DependencySetFactory,
    ) -> Vec<(Vec<TableauObject>, bool)> {
        let start = level * 3;
        let new_after_delta_new = self.indices_by_branching_point[start + 2];
        let mut removed = Vec::new();
        let mut tuple_index = self.after_delta_new;
        while tuple_index > new_after_delta_new {
            tuple_index -= 1;
            let tuple: Vec<TableauObject> = self
                .tuple_table
                .retrieve_tuple(tuple_index)
                .into_iter()
                .map(|o| o.expect("tuple slot occupied"))
                .collect();
            let is_core = self.is_core(tuple_index);
            for index in self.tuple_indexes.iter_mut().rev() {
                index.remove_tuple(&tuple);
            }
            if self.needs_dependency_sets {
                if let Some(slot) = self.dependency_sets.get_mut(tuple_index) {
                    if let Some(dependency_set) = slot.take() {
                        factory.remove_usage(&dependency_set);
                    }
                }
            }
            self.tuple_table.nullify_tuple(tuple_index);
            removed.push((tuple, is_core));
        }
        self.tuple_table.truncate(new_after_delta_new);
        self.after_extension_old = self.indices_by_branching_point[start];
        self.after_extension_this = self.indices_by_branching_point[start + 1];
        self.after_delta_new = new_after_delta_new;
        removed
    }

    pub fn clear(&mut self) {
        self.tuple_table.clear();
        for index in &mut self.tuple_indexes {
            index.clear();
        }
        self.dependency_sets.clear();
        self.core_flags.clear();
        self.after_extension_old = 0;
        self.after_extension_this = 0;
        self.after_delta_new = 0;
    }

    /// The `[start, after_last)` tuple-index range for a retrieval view.
    pub fn view_range(&self, view: View) -> (usize, usize) {
        match view {
            View::ExtensionThis => (0, self.after_extension_this),
            View::ExtensionOld => (0, self.after_extension_old),
            View::DeltaOld => (self.after_extension_old, self.after_extension_this),
            View::Total => (0, self.after_delta_new),
        }
    }

    /// Indexed retrieval, mirroring `ExtensionTableWithTupleIndexes.createRetrieval`
    /// + `IndexedRetrieval`. Selects the tuple index whose indexing sequence has
    /// the longest bound *prefix* under `binding_positions` (iterating the indexes
    /// in reverse so ties resolve as in Java), walks that index's trie subtree,
    /// and returns the matching tuple indices that fall within `view`'s range, in
    /// trie (reverse-insertion) order. Returns `None` when no index has a bound
    /// leading column, signalling the caller to fall back to the ascending
    /// unindexed scan. `binding_positions[c]` is the index into `bindings_buffer`
    /// holding the value bound to column `c` (or -1 if column `c` is free).
    pub fn indexed_tuple_indices(
        &self,
        binding_positions: &[i32],
        bindings_buffer: &[Option<TableauObject>],
        view: View,
    ) -> Option<Vec<usize>> {
        let mut selected: Option<&TupleIndex<TableauObject>> = None;
        let mut best_prefix = 0usize;
        for tuple_index in self.tuple_indexes.iter().rev() {
            let sequence = tuple_index.get_indexing_sequence();
            let mut prefix = 0usize;
            for &column in sequence {
                if binding_positions[column] != -1 {
                    prefix += 1;
                } else {
                    break;
                }
            }
            if prefix > best_prefix {
                best_prefix = prefix;
                selected = Some(tuple_index);
            }
        }
        let tuple_index = selected?;
        let sequence = tuple_index.get_indexing_sequence();
        // The selection array holds the *buffer* indices for the bound prefix
        // (Java `createSelectionArray`: `bindingPositions[indexingSequence[i]]`).
        let selection_indices: Vec<usize> = sequence[..best_prefix]
            .iter()
            .map(|&column| binding_positions[column] as usize)
            .collect();
        // The trie walk only reads the bound-prefix buffer slots, all of which
        // are `Some`, so the retrieval borrows `bindings_buffer` directly rather
        // than cloning it into an owned per-call buffer.
        let (first, after_last) = self.view_range(view);
        let mut retrieval =
            TupleIndexRetrieval::new(tuple_index, bindings_buffer, selection_indices);
        retrieval.open();
        let mut result = Vec::new();
        while !retrieval.after_last() {
            let tuple = retrieval.get_current_tuple_index();
            if tuple >= 0 {
                let tuple = tuple as usize;
                if first <= tuple && tuple < after_last {
                    result.push(tuple);
                }
            }
            retrieval.next();
        }
        Some(result)
    }
}

/// Convenience: build the binary (concept, node) extension table.
pub fn new_binary_extension_table(needs_dependency_sets: bool) -> ExtensionTable {
    ExtensionTable::new(2, needs_dependency_sets, vec![vec![1, 0], vec![0, 1]], true)
}

/// Convenience: build the ternary (predicate, node, node) extension table.
pub fn new_ternary_extension_table(needs_dependency_sets: bool) -> ExtensionTable {
    ExtensionTable::new(
        3,
        needs_dependency_sets,
        vec![vec![0, 1, 2], vec![1, 2, 0], vec![2, 0, 1]],
        false,
    )
}

/// A materialized retrieval over an extension table: the matching tuple indices
/// within a view, computed up-front (which avoids holding a borrow of the table
/// across tableau mutation, while giving the same results as HermiT's lazy
/// cursor since views range over a fixed index window).
pub struct Retrieval {
    pub(crate) tuple_indices: Vec<usize>,
    pub(crate) position: usize,
    pub(crate) view: View,
}

impl Retrieval {
    pub fn after_last(&self) -> bool {
        self.position >= self.tuple_indices.len()
    }
    pub fn get_current_tuple_index(&self) -> usize {
        self.tuple_indices[self.position]
    }
    pub fn next(&mut self) {
        self.position += 1;
    }
    pub fn view(&self) -> View {
        self.view
    }
}
