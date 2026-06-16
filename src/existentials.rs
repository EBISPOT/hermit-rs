// Port of the org.semanticweb.HermiT.existentials package: the strategies that
// drive existential (`≥n R.C` / `≥n R.dr` / description-graph) expansion.
//
// HermiT factors existential expansion behind an `ExistentialExpansionStrategy`
// interface so different heuristics (breadth-first creation order, individual
// reuse) can be plugged in. The shared loop lives in `AbstractExpansionStrategy`;
// the concrete strategies differ only in `expandExistential`.
//
// This port keeps the actual expansion primitives on `Tableau`
// (`expand_existentials` realizes `CreationOrderStrategy`); the types here mirror
// HermiT's class structure and make the strategy choice explicit, with
// `IndividualReuseStrategy`'s reuse bookkeeping ported faithfully.
//
// `Configuration.existential_strategy_type` is honoured:
// `Tableau::set_existential_strategy` (called from `Tableau::with_configuration`)
// stores an `IndividualReuseStrategy` for the `IndividualReuse`/`El` choices,
// seeded from the `IndividualReuseStrategy.reuseAlways`/`.reuseNever` parameters,
// and `runCalculus` drives its `model_found` bookkeeping.
//
// When a reuse strategy is selected, `Tableau::expand_at_least_concept` routes
// `>=1 r.C` expansion through `try_parent_reuse` then `expand_with_model_reuse`
// (`src/tableau/existential_expansion.rs`), which reuse a single per-concept
// witness node instead of creating a fresh one — producing HermiT's smaller
// reuse-shaped model. `IndividualReuseBranchingPoint` is represented as the
// `reuse` variant of `BranchingPointData` (`src/tableau/branching.rs`): on a
// clash that depended on a reuse decision, `reuse_start_next_choice` backtracks
// the reuse, records the filler in `dont_reuse_this_run`, and retries with a
// fresh tree successor. The reuse table is branching-point-indexed and backtracks
// with the tableau (`branching_point_pushed`/`backtrack`).
//
// This keeps `IndividualReuse` (non-deterministic) sound+complete: it decides
// exactly the same consistency / classification questions as the default
// `CreationOrderStrategy`, differing only in model SHAPE (smaller, witness-
// sharing). The default creation-order path is unchanged (no reuse strategy
// installed -> the dispatch falls straight through to `do_normal_at_least_
// expansion`). The deterministic `El` strategy pushes no branching point (Java
// `!m_isDeterministic` guard), so — like Java — it is only complete on EL-profile
// ontologies.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::model::AtomicConcept;
use crate::tableau::node::NodeId;

/// The set of concepts that must never be reused again, shared across every
/// per-test tableau of one reasoner so the learning HermiT keeps on its single
/// long-lived `m_tableau` (folding `m_dontReuseConceptsThisRun` into
/// `m_dontReuseConceptsEver` on each `modelFound`) persists across satisfiability
/// tests rather than being lost when each fresh tableau builds a new strategy.
pub type SharedDontReuseEver = Rc<RefCell<HashSet<AtomicConcept>>>;

/// Three-valued result of `AbstractExpansionStrategy.isSatisfied`: an
/// existential may be unsatisfied, permanently satisfied (by a non-nominal
/// witness), or only currently satisfied (by a nominal, so the NN/NI rule may
/// later force re-expansion).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatisfactionResult {
    NotSatisfied,
    PermanentlySatisfied,
    CurrentlySatisfied,
}

/// Port of `ExistentialExpansionStrategy` (the reasoning-relevant subset). The
/// node-lifecycle / assertion callbacks HermiT forwards to the blocking
/// strategy are handled directly by the `Tableau` in this port.
pub trait ExistentialExpansionStrategy {
    /// Expands existentials over the tableau; returns whether anything changed.
    fn expand_existentials(&mut self, tableau: &mut crate::tableau::tableau::Tableau) -> bool;
    /// Whether the strategy introduces no non-determinism.
    fn is_deterministic(&self) -> bool;
    /// Whether the strategy is exact (builds a model without over-approximation).
    fn is_exact(&self) -> bool;
}

/// Port of `CreationOrderStrategy`: expand all existentials on the oldest node
/// with unprocessed existentials (closely breadth-first). This is the default
/// strategy, and the behaviour the `Tableau`'s `expand_existentials` already
/// implements; this wrapper makes the choice explicit.
#[derive(Default)]
pub struct CreationOrderStrategy;

impl ExistentialExpansionStrategy for CreationOrderStrategy {
    fn expand_existentials(&mut self, tableau: &mut crate::tableau::tableau::Tableau) -> bool {
        tableau.expand_existentials()
    }
    fn is_deterministic(&self) -> bool {
        true
    }
    fn is_exact(&self) -> bool {
        true
    }
}

/// Port of `IndividualReuseStrategy`: instead of always creating a fresh witness
/// for `≥1 R.C`, reuse a single representative node per (atomic, non-internal)
/// concept `C`, keeping the model finite for many ontologies. The reuse table is
/// branching-point indexed so it backtracks with the tableau.
///
/// This ports the strategy's bookkeeping (the reuse map, the always/never-reuse
/// concept sets, and the backtracking of reused nodes); the actual node creation
/// stays on the `Tableau`.
pub struct IndividualReuseStrategy {
    is_deterministic: bool,
    /// The representative node reused for each concept, with the branching point
    /// at which it was introduced.
    reused_nodes: HashMap<AtomicConcept, (NodeId, i32)>,
    do_reuse_always: HashSet<AtomicConcept>,
    dont_reuse_this_run: HashSet<AtomicConcept>,
    dont_reuse_ever: SharedDontReuseEver,
    /// Concepts whose reuse node was introduced, indexed by branching point for
    /// backtracking (`m_reuseBacktrackingTable` + `m_indicesByBranchingPoint`).
    reuse_backtracking: Vec<AtomicConcept>,
    indices_by_branching_point: Vec<usize>,
}

impl IndividualReuseStrategy {
    pub fn new(is_deterministic: bool) -> IndividualReuseStrategy {
        IndividualReuseStrategy {
            is_deterministic,
            reused_nodes: HashMap::new(),
            do_reuse_always: HashSet::new(),
            dont_reuse_this_run: HashSet::new(),
            dont_reuse_ever: Rc::new(RefCell::new(HashSet::new())),
            reuse_backtracking: Vec::new(),
            indices_by_branching_point: Vec::new(),
        }
    }

    /// Port of `IndividualReuseStrategy.initialize`: builds the strategy and seeds
    /// the always/never-reuse concept sets from the tableau parameters
    /// (`IndividualReuseStrategy.reuseAlways` / `.reuseNever`). The
    /// [`Configuration`](crate::configuration::Configuration) stores those concept
    /// sets as newline-joined IRIs (see `set_individual_reuse_strategy_reuse_*`).
    pub fn from_parameters(
        is_deterministic: bool,
        parameters: &HashMap<String, String>,
    ) -> IndividualReuseStrategy {
        let mut strategy = IndividualReuseStrategy::new(is_deterministic);
        let parse = |key: &str| -> HashSet<AtomicConcept> {
            parameters
                .get(key)
                .map(|joined| {
                    joined
                        .split('\n')
                        .filter(|iri| !iri.is_empty())
                        .map(|iri| AtomicConcept::create(iri.to_string()))
                        .collect()
                })
                .unwrap_or_default()
        };
        strategy.do_reuse_always = parse("IndividualReuseStrategy.reuseAlways");
        strategy.dont_reuse_ever.borrow_mut().extend(parse("IndividualReuseStrategy.reuseNever"));
        // `clear()` is run before each reasoning task: seed this-run from ever.
        strategy.dont_reuse_this_run = strategy.dont_reuse_ever.borrow().clone();
        strategy
    }

    /// Adopts a reasoner-wide shared never-reuse set (`m_dontReuseConceptsEver`),
    /// merging in any reuseNever concepts already parsed for this strategy and
    /// re-seeding this run from the shared set. This is how the cross-test learning
    /// persists when each satisfiability test builds a fresh tableau/strategy.
    pub fn adopt_shared_dont_reuse_ever(&mut self, shared: SharedDontReuseEver) {
        {
            let mut shared_set = shared.borrow_mut();
            shared_set.extend(self.dont_reuse_ever.borrow().iter().cloned());
        }
        self.dont_reuse_ever = shared;
        self.dont_reuse_this_run = self.dont_reuse_ever.borrow().clone();
    }

    pub fn clear(&mut self) {
        self.reused_nodes.clear();
        self.reuse_backtracking.clear();
        self.dont_reuse_this_run = self.dont_reuse_ever.borrow().clone();
    }

    /// Whether this reuse strategy introduces no non-determinism (the `EL`
    /// strategy is deterministic, plain `IndividualReuse` is not). When it is
    /// deterministic, HermiT's `tryParentReuse`/`expandWithModelReuse` never push
    /// an `IndividualReuseBranchingPoint`.
    pub fn is_deterministic_strategy(&self) -> bool {
        self.is_deterministic
    }

    /// `getConceptForNode`: the concept whose reuse representative is `node`.
    pub fn concept_for_node(&self, node: NodeId) -> Option<AtomicConcept> {
        self.reused_nodes
            .iter()
            .find(|(_, (n, _))| *n == node)
            .map(|(c, _)| c.clone())
    }

    /// Whether `concept` is eligible for model reuse (`expandWithModelReuse`'s
    /// guard): an atomic, non-internal concept that is not on the never-reuse
    /// list for this run (unless forced by the always-reuse list).
    pub fn should_reuse(&self, concept: &AtomicConcept) -> bool {
        if concept.iri().starts_with("internal:") {
            return false;
        }
        self.do_reuse_always.contains(concept) || !self.dont_reuse_this_run.contains(concept)
    }

    /// Records the reuse representative for `concept` at `branching_point`.
    pub fn record_reuse(&mut self, concept: AtomicConcept, node: NodeId, branching_point: i32) {
        self.reused_nodes.insert(concept.clone(), (node, branching_point));
        self.reuse_backtracking.push(concept);
    }

    /// The reuse representative recorded for `concept`, if any, together with the
    /// branching-point level at which it was introduced (`NodeBranchingPointPair`).
    pub fn reuse_info(&self, concept: &AtomicConcept) -> Option<(NodeId, i32)> {
        self.reused_nodes.get(concept).copied()
    }

    /// The reuse representative recorded for `concept`, if any.
    pub fn reuse_node(&self, concept: &AtomicConcept) -> Option<NodeId> {
        self.reused_nodes.get(concept).map(|(node, _)| *node)
    }

    /// `IndividualReuseBranchingPoint.startNextChoice`'s
    /// `m_dontReuseConceptsThisRun.add(...)`: mark `concept` not to be reused
    /// again for the remainder of this reasoning run (it clashed under reuse).
    pub fn add_dont_reuse_this_run(&mut self, concept: AtomicConcept) {
        self.dont_reuse_this_run.insert(concept);
    }

    /// `branchingPointPushed`: remember the reuse-table watermark for `level`.
    pub fn branching_point_pushed(&mut self, level: usize) {
        if level >= self.indices_by_branching_point.len() {
            self.indices_by_branching_point.resize(level + 1, 0);
        }
        self.indices_by_branching_point[level] = self.reuse_backtracking.len();
    }

    /// `backtrack`: drop the reuse representatives introduced after `level`.
    pub fn backtrack(&mut self, level: usize) {
        let watermark = self.indices_by_branching_point[level];
        for concept in self.reuse_backtracking.drain(watermark..) {
            self.reused_nodes.remove(&concept);
        }
    }

    /// `modelFound`: concepts not reused this run are never reused again.
    pub fn model_found(&mut self) {
        self.dont_reuse_ever
            .borrow_mut()
            .extend(self.dont_reuse_this_run.iter().cloned());
    }
}

impl ExistentialExpansionStrategy for IndividualReuseStrategy {
    fn expand_existentials(&mut self, tableau: &mut crate::tableau::tableau::Tableau) -> bool {
        // The reuse heuristic shares the same node-walk as creation order; the
        // per-existential dispatch in `Tableau::expand_at_least_concept` routes
        // `>=1 r.C` through `try_parent_reuse`/`expand_with_model_reuse` when this
        // strategy is installed, falling back to creation-order expansion only for
        // the existentials it does not reuse.
        tableau.expand_existentials()
    }
    fn is_deterministic(&self) -> bool {
        self.is_deterministic
    }
    fn is_exact(&self) -> bool {
        // Individual reuse over-approximates the model (it is not exact).
        false
    }
}

// --- Port of `AbstractExpansionStrategy`'s satisfaction-check combinatorics.
//
// The `expandExistentials` loop and the extension-table side of `isSatisfied`
// are realized directly by the `Tableau` (`tableau::existential_expansion`).
// The two distinctive, self-contained helpers below — the "permanent satisfier"
// test and the "exists a subset of `n` pairwise-unequal witnesses" search used
// by `isSatisfied` for `≥n R.C` with `n > 1` — are ported here, parameterized by
// oracles so they are independent of the engine's node representation.

/// Port of `AbstractExpansionStrategy.isPermanentSatisfier`: a witness counts as
/// a permanent satisfier of `for_node`'s existential when it is `for_node`
/// itself, the parent or a child of `for_node`, or a root (nominal) node. The
/// caller supplies `parent_of` (a node's parent, if any) and `is_root`.
pub fn is_permanent_satisfier<F, G>(
    for_node: NodeId,
    to_node: NodeId,
    parent_of: F,
    is_root: G,
) -> bool
where
    F: Fn(NodeId) -> Option<NodeId>,
    G: Fn(NodeId) -> bool,
{
    for_node == to_node
        || parent_of(for_node) == Some(to_node)
        || parent_of(to_node) == Some(for_node)
        || is_root(to_node)
}

/// Port of `AbstractExpansionStrategy.containsSubsetOfNUnequalNodes`: whether
/// `nodes` contains a subset of `cardinality` nodes that are pairwise unequal
/// (an explicit `≠` assertion in either direction), via the same backtracking
/// search HermiT uses. `unequal(a, b)` is the inequality oracle.
pub fn contains_subset_of_n_unequal_nodes<F>(
    nodes: &[NodeId],
    cardinality: usize,
    unequal: &F,
) -> bool
where
    F: Fn(NodeId, NodeId) -> bool,
{
    fn search<F>(
        nodes: &[NodeId],
        start_at: usize,
        selected: &mut Vec<NodeId>,
        cardinality: usize,
        unequal: &F,
    ) -> bool
    where
        F: Fn(NodeId, NodeId) -> bool,
    {
        if selected.len() == cardinality {
            return true;
        }
        'outer: for index in start_at..nodes.len() {
            let node = nodes[index];
            for &chosen in selected.iter() {
                // Skip `node` if it is not provably unequal to an already-chosen one.
                if !unequal(node, chosen) && !unequal(chosen, node) {
                    continue 'outer;
                }
            }
            selected.push(node);
            if search(nodes, index + 1, selected, cardinality, unequal) {
                return true;
            }
            selected.pop();
        }
        false
    }
    let mut selected: Vec<NodeId> = Vec::new();
    search(nodes, 0, &mut selected, cardinality, unequal)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn concept(name: &str) -> AtomicConcept {
        AtomicConcept::create(format!("http://example.org/{name}"))
    }

    #[test]
    fn reuse_bookkeeping_backtracks() {
        let mut strategy = IndividualReuseStrategy::new(true);
        // Internal concepts are never reused.
        assert!(!strategy.should_reuse(&AtomicConcept::create("internal:nom#x")));
        assert!(strategy.should_reuse(&concept("C")));

        strategy.branching_point_pushed(0);
        strategy.record_reuse(concept("C"), 7, 0);
        assert_eq!(strategy.reuse_node(&concept("C")), Some(7));
        assert_eq!(strategy.concept_for_node(7), Some(concept("C")));

        // Pushing a deeper branching point and reusing another concept, then
        // backtracking to level 0, drops the level-0+ reuses.
        strategy.branching_point_pushed(1);
        strategy.record_reuse(concept("D"), 9, 1);
        strategy.backtrack(0);
        assert_eq!(strategy.reuse_node(&concept("C")), None);
        assert_eq!(strategy.reuse_node(&concept("D")), None);
    }

    #[test]
    fn permanent_satisfier_recognises_parent_child_and_roots() {
        // parent_of: 1's parent is 0; 2 is a root with no parent.
        let parent_of = |n: NodeId| if n == 1 { Some(0) } else { None };
        let is_root = |n: NodeId| n == 2;
        // self
        assert!(is_permanent_satisfier(5, 5, parent_of, is_root));
        // to_node is the parent of for_node
        assert!(is_permanent_satisfier(1, 0, parent_of, is_root));
        // to_node is a child of for_node (for_node is to_node's parent)
        assert!(is_permanent_satisfier(0, 1, parent_of, is_root));
        // to_node is a root
        assert!(is_permanent_satisfier(9, 2, parent_of, is_root));
        // none of the above
        assert!(!is_permanent_satisfier(7, 8, parent_of, is_root));
    }

    #[test]
    fn subset_of_n_unequal_nodes_search() {
        // Inequalities: 10≠11, 10≠12, 11≠12 (all distinct); 13 equal to all.
        let pairs: HashSet<(NodeId, NodeId)> =
            [(10, 11), (10, 12), (11, 12)].into_iter().collect();
        let unequal = |a: NodeId, b: NodeId| pairs.contains(&(a, b)) || pairs.contains(&(b, a));

        // {10,11,12} contains 3 pairwise-unequal nodes.
        assert!(contains_subset_of_n_unequal_nodes(&[10, 11, 12], 3, &unequal));
        // Adding 13 (equal to everything) still gives a 3-subset from {10,11,12}.
        assert!(contains_subset_of_n_unequal_nodes(&[10, 11, 12, 13], 3, &unequal));
        // But there is no 4-subset of pairwise-unequal nodes.
        assert!(!contains_subset_of_n_unequal_nodes(&[10, 11, 12, 13], 4, &unequal));
        // No two of {13,14} are provably unequal, so no 2-subset.
        assert!(!contains_subset_of_n_unequal_nodes(&[13, 14], 2, &unequal));
    }

    #[test]
    fn creation_order_is_deterministic_and_exact() {
        let strategy = CreationOrderStrategy;
        assert!(strategy.is_deterministic());
        assert!(strategy.is_exact());
        let reuse = IndividualReuseStrategy::new(false);
        assert!(!reuse.is_deterministic());
        assert!(!reuse.is_exact());
    }
}
