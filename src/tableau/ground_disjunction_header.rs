// Port of org.semanticweb.HermiT.tableau.GroundDisjunctionHeader.
//
// Describes the predicate structure shared by ground disjunctions with the same
// sequence of head predicates: the per-disjunct argument offsets, and a
// heuristic ordering of the disjuncts (partitioned into atomic, at-least over a
// negated atomic concept, and other at-least disjuncts) that adapts to the
// number of backtrackings seen for each disjunct.

use crate::model::{DLPredicate, LiteralConcept};
use crate::prefixes::Prefixes;

struct DisjunctIndexWithBacktrackings {
    disjunct_index: usize,
    number_of_backtrackings: i32,
}

pub struct GroundDisjunctionHeader {
    dl_predicates: Vec<DLPredicate>,
    disjunct_start: Vec<usize>,
    disjunct_indexes_with_backtrackings: Vec<DisjunctIndexWithBacktrackings>,
    first_at_least_positive_index: usize,
    first_at_least_negative_index: usize,
}

fn is_at_least_over_negated_atomic(predicate: &DLPredicate) -> Option<bool> {
    // Returns Some(true) for an at-least over a negated atomic concept,
    // Some(false) for any other at-least concept, None if not an at-least.
    match predicate {
        DLPredicate::AtLeastConcept(at_least) => Some(matches!(
            at_least.to_concept(),
            LiteralConcept::AtomicNegationConcept(_)
        )),
        _ => None,
    }
}

impl GroundDisjunctionHeader {
    pub fn new(dl_predicates: Vec<DLPredicate>) -> GroundDisjunctionHeader {
        let mut disjunct_start = vec![0usize; dl_predicates.len()];
        let mut arguments_size = 0;
        for (disjunct_index, predicate) in dl_predicates.iter().enumerate() {
            disjunct_start[disjunct_index] = arguments_size;
            arguments_size += predicate.arity();
        }

        let mut number_of_at_least_positive = 0usize;
        let mut number_of_at_least_negative = 0usize;
        for predicate in &dl_predicates {
            match is_at_least_over_negated_atomic(predicate) {
                Some(true) => number_of_at_least_negative += 1,
                Some(false) => number_of_at_least_positive += 1,
                None => {}
            }
        }
        let length = dl_predicates.len();
        let first_at_least_negative_index =
            length - number_of_at_least_positive - number_of_at_least_negative;
        let first_at_least_positive_index = length - number_of_at_least_positive;

        let mut slots: Vec<Option<DisjunctIndexWithBacktrackings>> =
            (0..length).map(|_| None).collect();
        let mut next_atomic = 0usize;
        let mut next_at_least_negative = first_at_least_negative_index;
        let mut next_at_least_positive = first_at_least_positive_index;
        for (index, predicate) in dl_predicates.iter().enumerate() {
            let entry = DisjunctIndexWithBacktrackings {
                disjunct_index: index,
                number_of_backtrackings: 0,
            };
            match is_at_least_over_negated_atomic(predicate) {
                Some(true) => {
                    slots[next_at_least_negative] = Some(entry);
                    next_at_least_negative += 1;
                }
                Some(false) => {
                    slots[next_at_least_positive] = Some(entry);
                    next_at_least_positive += 1;
                }
                None => {
                    slots[next_atomic] = Some(entry);
                    next_atomic += 1;
                }
            }
        }
        let disjunct_indexes_with_backtrackings =
            slots.into_iter().map(|s| s.unwrap()).collect();

        GroundDisjunctionHeader {
            dl_predicates,
            disjunct_start,
            disjunct_indexes_with_backtrackings,
            first_at_least_positive_index,
            first_at_least_negative_index,
        }
    }

    pub fn dl_predicates(&self) -> &[DLPredicate] {
        &self.dl_predicates
    }
    pub fn disjunct_start(&self, disjunct_index: usize) -> usize {
        self.disjunct_start[disjunct_index]
    }

    pub fn is_equal(&self, dl_predicates: &[DLPredicate]) -> bool {
        self.dl_predicates == dl_predicates
    }

    pub fn get_sorted_disjunct_indexes(&self) -> Vec<usize> {
        self.disjunct_indexes_with_backtrackings
            .iter()
            .map(|d| d.disjunct_index)
            .collect()
    }

    pub fn increase_number_of_backtrackings(&mut self, disjunct_index: usize) {
        let length = self.disjunct_indexes_with_backtrackings.len();
        let Some(index) = self
            .disjunct_indexes_with_backtrackings
            .iter()
            .position(|d| d.disjunct_index == disjunct_index)
        else {
            return;
        };
        self.disjunct_indexes_with_backtrackings[index].number_of_backtrackings += 1;
        // The partition end: disjuncts only move within their partition.
        let partition_end = if index < self.first_at_least_negative_index {
            self.first_at_least_negative_index
        } else if index < self.first_at_least_positive_index {
            self.first_at_least_positive_index
        } else {
            length
        };
        let mut current_index = index;
        let mut next_index = current_index + 1;
        while next_index < partition_end
            && self.disjunct_indexes_with_backtrackings[current_index].number_of_backtrackings
                > self.disjunct_indexes_with_backtrackings[next_index].number_of_backtrackings
        {
            self.disjunct_indexes_with_backtrackings
                .swap(current_index, next_index);
            current_index = next_index;
            next_index += 1;
        }
    }

    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        let mut buffer = String::new();
        for (disjunct_index, predicate) in self.dl_predicates.iter().enumerate() {
            if disjunct_index > 0 {
                buffer.push_str(" \\/ ");
            }
            buffer.push_str(&predicate.to_string_prefixes(prefixes));
            buffer.push_str(" (");
            if let Some(entry) = self
                .disjunct_indexes_with_backtrackings
                .iter()
                .find(|d| d.disjunct_index == disjunct_index)
            {
                buffer.push_str(&entry.number_of_backtrackings.to_string());
            }
            buffer.push(')');
        }
        buffer
    }
}

impl std::fmt::Display for GroundDisjunctionHeader {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_prefixes(Prefixes::standard()))
    }
}
