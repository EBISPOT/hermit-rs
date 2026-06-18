// Ports of the supporting managers of
// org.semanticweb.HermiT.tableau.DLClauseEvaluator:
//   * ValuesBufferManager -- computes the shared "values buffer" layout used by
//     the compiled clause evaluators (one slot per body variable, plus a slot
//     per distinct body DL predicate and per non-variable body term).
//   * GroundDisjunctionHeaderManager -- interns GroundDisjunctionHeaders by
//     their head-predicate sequence.
//
// The compiled-clause evaluator VM itself (the Worker program + DLClauseCompiler)
// is the next part of the hyperresolution engine; these layout/intern managers
// are its foundation.
#![allow(dead_code)]

use std::cell::RefCell;
use rustc_hash::FxHashMap as HashMap;
use std::rc::Rc;

use crate::model::{Concept, DLClause, DLPredicate, Term};
use crate::tableau::ground_disjunction_header::GroundDisjunctionHeader;
use crate::tableau::node::NodeId;
use crate::tableau::object::TableauObject;

/// Maps a DL predicate to the label form under which it is stored in an
/// extension table: concept-like predicates are stored under the `Concept`
/// label (matching how the engine stores and looks up concept assertions),
/// everything else as a DL predicate.
pub(crate) fn predicate_to_stored_label(predicate: &DLPredicate) -> TableauObject {
    match predicate {
        DLPredicate::AtomicConcept(c) => TableauObject::Concept(Concept::AtomicConcept(c.clone())),
        DLPredicate::AtLeastConcept(c) => {
            TableauObject::Concept(Concept::AtLeastConcept(c.clone()))
        }
        DLPredicate::AtLeastDataRange(c) => {
            TableauObject::Concept(Concept::AtLeastDataRange(c.clone()))
        }
        DLPredicate::ExistsDescriptionGraph(c) => {
            TableauObject::Concept(Concept::ExistsDescriptionGraph(c.clone()))
        }
        other => TableauObject::DLPredicate(other.clone()),
    }
}

/// Port of DLClauseEvaluator.ValuesBufferManager.
pub struct ValuesBufferManager {
    /// The single, shared values buffer. HermiT keeps **one** `Object[] m_valuesBuffer`
    /// in the manager and hands every compiled `DLClauseEvaluator` a *reference* to
    /// it (the evaluators run sequentially over one tableau, so the scratch
    /// variable slots are simply overwritten per run and the ground predicate/term
    /// slots are read-only constants). Sharing via `Rc<RefCell<…>>` reproduces that:
    /// without it, each of the (tens of thousands of) evaluators cloned the whole
    /// global-width buffer — ~1.8 MB each on EFO — which alone exhausted memory
    /// before any reasoning began.
    pub values_buffer: Rc<RefCell<Vec<Option<TableauObject>>>>,
    pub body_dl_predicates_to_indexes: HashMap<DLPredicate, usize>,
    pub max_number_of_variables: usize,
    pub body_nonvariable_terms_to_indexes: HashMap<Term, usize>,
}

impl ValuesBufferManager {
    pub fn new<S: std::hash::BuildHasher>(
        dl_clauses: &[DLClause],
        terms_to_nodes: &std::collections::HashMap<Term, NodeId, S>,
    ) -> Result<ValuesBufferManager, String> {
        // First pass: collect the distinct body predicates, the maximum number
        // of distinct variables in any one clause body, and the non-variable
        // body terms.
        let mut body_dl_predicates: Vec<DLPredicate> = Vec::new();
        let mut body_dl_predicate_set: std::collections::HashSet<DLPredicate> =
            std::collections::HashSet::default();
        let mut nonvariable_terms: Vec<Term> = Vec::new();
        let mut nonvariable_term_set: std::collections::HashSet<Term> =
            std::collections::HashSet::default();
        let mut max_number_of_variables = 0usize;

        for dl_clause in dl_clauses {
            let mut variables: std::collections::HashSet<Term> = std::collections::HashSet::default();
            for body_index in 0..dl_clause.get_body_length() {
                let atom = dl_clause.get_body_atom(body_index);
                let predicate = atom.get_dl_predicate().clone();
                if body_dl_predicate_set.insert(predicate.clone()) {
                    body_dl_predicates.push(predicate);
                }
                for argument_index in 0..atom.get_arity() {
                    let term = atom.get_argument(argument_index).clone();
                    if matches!(term, Term::Variable(_)) {
                        variables.insert(term);
                    } else if nonvariable_term_set.insert(term.clone()) {
                        nonvariable_terms.push(term);
                    }
                }
            }
            max_number_of_variables = max_number_of_variables.max(variables.len());
        }

        let buffer_len =
            max_number_of_variables + body_dl_predicates.len() + nonvariable_terms.len();
        let mut values_buffer: Vec<Option<TableauObject>> = vec![None; buffer_len];

        let mut body_dl_predicates_to_indexes: HashMap<DLPredicate, usize> = HashMap::default();
        let mut binding_index = max_number_of_variables;
        for predicate in body_dl_predicates {
            let label = predicate_to_stored_label(&predicate);
            body_dl_predicates_to_indexes.insert(predicate, binding_index);
            values_buffer[binding_index] = Some(label);
            binding_index += 1;
        }

        let mut body_nonvariable_terms_to_indexes: HashMap<Term, usize> = HashMap::default();
        for term in nonvariable_terms {
            match terms_to_nodes.get(&term) {
                None => {
                    return Err(format!("Term '{term}' is unknown to the reasoner."));
                }
                Some(&node) => {
                    body_nonvariable_terms_to_indexes.insert(term, binding_index);
                    values_buffer[binding_index] = Some(TableauObject::Node(node));
                    binding_index += 1;
                }
            }
        }

        Ok(ValuesBufferManager {
            values_buffer: Rc::new(RefCell::new(values_buffer)),
            body_dl_predicates_to_indexes,
            max_number_of_variables,
            body_nonvariable_terms_to_indexes,
        })
    }
}

/// Port of DLClauseEvaluator.GroundDisjunctionHeaderManager: interns
/// `GroundDisjunctionHeader`s by their predicate sequence, returning a stable
/// index into the manager (the headers are mutable -- their disjunct order
/// adapts to backtracking counts -- so callers refer to them by index).
#[derive(Default)]
pub struct GroundDisjunctionHeaderManager {
    headers: Vec<GroundDisjunctionHeader>,
    index: HashMap<Vec<DLPredicate>, usize>,
}

impl GroundDisjunctionHeaderManager {
    pub fn new() -> GroundDisjunctionHeaderManager {
        GroundDisjunctionHeaderManager::default()
    }

    /// Returns the index of the interned header for `dl_predicates`.
    pub fn get(&mut self, dl_predicates: Vec<DLPredicate>) -> usize {
        if let Some(&existing) = self.index.get(&dl_predicates) {
            return existing;
        }
        let header = GroundDisjunctionHeader::new(dl_predicates.clone());
        let idx = self.headers.len();
        self.headers.push(header);
        self.index.insert(dl_predicates, idx);
        idx
    }

    pub fn header(&self, index: usize) -> &GroundDisjunctionHeader {
        &self.headers[index]
    }
    pub fn header_mut(&mut self, index: usize) -> &mut GroundDisjunctionHeader {
        &mut self.headers[index]
    }
    pub fn len(&self) -> usize {
        self.headers.len()
    }
    pub fn is_empty(&self) -> bool {
        self.headers.is_empty()
    }
}
