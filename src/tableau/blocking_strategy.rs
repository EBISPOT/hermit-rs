// Pairwise (double) direct blocking, a port of
// org.semanticweb.HermiT.blocking.PairWiseDirectBlockingChecker driving an
// "anywhere" blocking pass (the `AnywhereBlocking` strategy specialized to the
// pairwise checker).
//
// A tree node `y` is (directly) blocked by an earlier, unblocked tree node `x`
// when their *pairwise signatures* coincide: equal atomic-concept labels, equal
// parent atomic-concept labels, and equal edge labels in both directions
// (parent→node and node→parent). This is the classical double-blocking
// condition that is sound and complete for SHIQ — i.e. it remains complete in
// the presence of inverse roles and number restrictions, unlike single
// (concept-label-only) blocking, which is complete only without inverse roles.
//
// Only tree nodes whose parent is a tree or graph node may participate
// (`canBeBlocker`/`canBeBlocked`); blocked nodes' existentials are not expanded,
// which guarantees termination because the number of distinct pairwise
// signatures over a finite vocabulary is finite.
//
// HermiT's validated blocking (`AnywhereValidatedBlocking` + `BlockingValidator`)
// is a further optimization layered on top of this; it IS ported
// (`compute_blocking_validated` here + `blocking_validator.rs`) and is enabled when
// a `BlockingValidator` is attached to the `Tableau`. The default is the pairwise
// `AnywhereBlocking` path, matching HermiT's `OPTIMAL` default for SHIQ/SHOIQ.
#![allow(dead_code)]

use crate::blocking::CachedSignature;
use crate::model::{AtomicConcept, AtomicRole, DLPredicate};
use crate::tableau::node::NodeId;
use crate::tableau::node_type::NodeType;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;
use crate::tableau::View;

/// The validated-blocking core signature: the node's core atomic-concept label,
/// plus (under pairwise blocking) the parent's core label. Label sets are sorted,
/// de-duplicated `Vec`s (see `CachedSignature`): used only for equality/hashing.
pub(crate) type ValidatedSignature =
    (Vec<AtomicConcept>, Option<Vec<AtomicConcept>>);

/// The pairwise blocking signature: (node label, parent label, parent→node edge
/// roles, node→parent edge roles). Each is a sorted, de-duplicated `Vec`.
type PairwiseSignature = (
    Vec<AtomicConcept>,
    Vec<AtomicConcept>,
    Vec<AtomicRole>,
    Vec<AtomicRole>,
);

/// The direct-blocking signature in use (port of HermiT's
/// `DirectBlockingChecker` implementations). `Single` blocks two tree nodes that
/// have equal atomic-concept labels (`SingleDirectBlockingChecker`); `Pairwise`
/// additionally requires equal parent labels and equal edge labels in both
/// directions (`PairWiseDirectBlockingChecker`). Single blocking is complete only
/// without inverse roles, which is exactly when HermiT's `OPTIMAL` selects it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectBlockingKind {
    Single,
    Pairwise,
}

/// The selected blocking strategy (port of HermiT's
/// `BlockingStrategy` implementations). `Anywhere` is the default
/// (`AnywhereBlocking`): a node may be blocked by *any* earlier unblocked node
/// with the same signature. `Ancestor` (`AncestorBlocking`) restricts blockers to
/// the node's own ancestor chain. `ValidatedCore` is `AnywhereValidatedBlocking`:
/// it pre-blocks on the weaker *core* label and validates blocks before
/// termination (the `simple` flag is the SIMPLE-core vs COMPLEX-core distinction).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockingStrategyKind {
    Anywhere,
    Ancestor,
    ValidatedCore { simple: bool },
}

impl Tableau {
    /// Whether the blocking strategy (hence the expansion strategy) is *exact*:
    /// it establishes only valid blocks, so a saturated tableau with no clash is
    /// a genuine model and no final-chance revalidation pass is needed
    /// (`AbstractExpansionStrategy.isExact` == `BlockingStrategy.isExact`).
    ///
    /// `AnywhereBlocking` (the default pairwise/double anywhere blocking) returns
    /// `true`; `AnywhereValidatedBlocking` (the validated/core strategy enabled by
    /// `set_blocking_validator`) returns `false`, since it pre-blocks with a weaker
    /// candidate condition and only validates blocks on demand. Mirrors HermiT's
    /// `m_blockingStrategy.isExact()`.
    pub fn is_exact(&self) -> bool {
        // The validated/core strategy (`AnywhereValidatedBlocking`) is inexact;
        // `Anywhere` and `Ancestor` are exact (their `isExact()` return `true`).
        // The validator presence is the operative signal -- it is attached iff a
        // core strategy is selected.
        self.blocking_validator.is_none()
    }

    /// Recomputes blocking over all nodes (called before existential expansion).
    ///
    /// `final_chance` mirrors `BlockingStrategy.computeBlocking(finalChance)`. For
    /// the exact pairwise strategy the flag is ignored (HermiT's `AnywhereBlocking`
    /// ignores it too). For the inexact validated strategy, the regular pass
    /// pre-blocks *and* validates here (a sound superset of HermiT's split where
    /// `computeBlocking(false)=computePreBlocking()` and
    /// `computeBlocking(true)=validateBlocks()`), so the final-chance pass simply
    /// re-runs the validating pass to catch any blocks that became invalid.
    pub fn compute_blocking(&mut self) {
        self.compute_blocking_with(false);
    }

    /// `compute_blocking` with the `finalChance` flag exposed. Dispatches on the
    /// configured strategy, mirroring `Reasoner.createTableau`'s choice of
    /// `BlockingStrategy`:
    ///   * `ValidatedCore` (`AnywhereValidatedBlocking`) -> the validated pass.
    ///   * `Ancestor`      (`AncestorBlocking`)          -> the ancestor pass.
    ///   * `Anywhere`      (`AnywhereBlocking`)          -> the anywhere pass.
    pub fn compute_blocking_with(&mut self, final_chance: bool) {
        // The validator is the operative inexactness signal; a core strategy is
        // selected iff one is attached. `AnywhereValidatedBlocking.computeBlocking`
        // pre-blocks during normal expansion and validates only on the final
        // chance (`finalChance ? validateBlocks() : computePreBlocking()`).
        if self.blocking_validator.is_some() {
            if final_chance {
                self.validate_blocks();
            } else {
                self.compute_pre_blocking();
            }
            return;
        }
        match self.blocking_strategy_kind {
            BlockingStrategyKind::Ancestor => self.compute_blocking_ancestor(),
            BlockingStrategyKind::Anywhere | BlockingStrategyKind::ValidatedCore { .. } => {
                self.compute_blocking_anywhere()
            }
        }
    }

    /// Anywhere blocking (`AnywhereBlocking.computeBlocking`) over the configured
    /// direct-blocking checker (single or pairwise). A node may be blocked by any
    /// earlier unblocked node with the same direct-blocking signature; a node
    /// whose parent is blocked is indirectly blocked and never offered as a
    /// blocker. When a signature cache is present and non-empty, a node whose
    /// signature is already cached is immediately blocked (Java's
    /// `Node.SIGNATURE_CACHE_BLOCKER` short-circuit).
    fn compute_blocking_anywhere(&mut self) {
        // Incremental recomputation (AnywhereBlocking.computeBlocking): only nodes
        // from `first_changed_node` onward can have changed, so nodes before it
        // keep their block status and their persistent blockers-cache entries.
        let Some(start) = self.first_changed_node else {
            return;
        };
        // First pass: drop every node from the changed point onward out of the
        // persistent blockers cache.
        let mut node = Some(start);
        while let Some(current) = node {
            self.blockers_cache_remove(current);
            node = self.nodes[current].next_tableau_node;
        }
        // Second pass: recompute the block status of those nodes, re-populating
        // the cache as their (now-current) signatures are seen. A directly blocked
        // node whose own info has not changed and whose blocker lies below the
        // changed range keeps its block without recomputation
        // (`AnywhereBlocking.computeBlocking`'s recompute guard).
        let start_id = self.nodes[start].node_id;
        let mut node = Some(start);
        while let Some(current) = node {
            if self.can_participate_in_blocking(current) {
                let recompute = self.nodes[current].has_blocking_info_changed
                    || !self.nodes[current].is_directly_blocked()
                    || match self.nodes[current].get_blocker() {
                        Some(b) => self.nodes[b].node_id >= start_id,
                        // A signature-cache block carries no concrete blocker node;
                        // HermiT's `SIGNATURE_CACHE_BLOCKER` sentinel has nodeID -1,
                        // so this term is false (a real first-changed node has id >= 0).
                        None => -1 >= start_id,
                    };
                if recompute {
                    // The unblocked `else`-branch below computes the node's
                    // direct-blocking signature for the cache lookup; stash it so the
                    // post-decision re-add does not recompute (and re-scan/re-clone)
                    // the very same signature. The parent-none branch leaves this
                    // `None` and computes the signature once at re-add time.
                    let mut computed_signature: Option<CachedSignature> = None;
                    let parent = self.nodes[current].get_parent();
                    if parent.is_none() {
                        self.nodes[current].set_blocked(None, false);
                    } else if parent.is_some_and(|p| self.nodes[p].is_blocked()) {
                        self.nodes[current].set_blocked(parent, false);
                    } else {
                        let signature = self.direct_signature(current);
                        if self.signature_is_cached(&signature) {
                            // Cache short-circuit: a previously-found model witnessed
                            // this signature, so block it directly. The blocker node is
                            // unknown (HermiT uses the sentinel `SIGNATURE_CACHE_BLOCKER`);
                            // mark it directly blocked with no concrete blocker node.
                            self.nodes[current].set_blocked(None, true);
                        } else if let Some(&blocker) =
                            self.blockers_cache_by_signature.get(&signature)
                        {
                            self.nodes[current].set_blocked(Some(blocker), true);
                        } else {
                            self.nodes[current].set_blocked(None, false);
                            computed_signature = Some(signature);
                        }
                    }
                    // A node left unblocked re-enters the blockers cache as a
                    // candidate blocker (Java's post-decision `if (!node.isBlocked()
                    // && canBeBlocker(node)) addNode(node)`).
                    if !self.nodes[current].is_blocked() {
                        let signature = match computed_signature {
                            Some(sig) => sig,
                            None => self.direct_signature(current),
                        };
                        self.blockers_cache_add(current, signature);
                        // A node that just became unblocked and still carries
                        // unprocessed existentials must be reconsidered by the
                        // expansion walk, so pull the cursor back to it (it may have
                        // been a blocked "wall" the cursor previously sat behind).
                        if self.nodes[current].has_unprocessed_existentials() {
                            self.note_unprocessed_existential(current);
                        }
                    }
                }
                self.nodes[current].has_blocking_info_changed = false;
            }
            node = self.nodes[current].next_tableau_node;
        }
        self.first_changed_node = None;
    }

    /// Records that `node`'s anywhere-blocking signature may have changed, so the
    /// next `compute_blocking_anywhere` reprocesses it (and every later node).
    /// `first_changed_node` tracks the lowest `node_id` so reprocessing starts no
    /// later than the earliest change (`AnywhereBlocking.updateNodeChange`).
    pub(crate) fn note_blocking_node_changed(&mut self, node: NodeId) {
        let id = self.nodes[node].node_id;
        let is_lower = match self.first_changed_node {
            None => true,
            Some(current) => id < self.nodes[current].node_id,
        };
        if is_lower {
            self.first_changed_node = Some(node);
        }
        // Invalidate this node's cached blocking labels and mark its info changed
        // (`DirectBlockingChecker.assertionAdded`/`assertionRemoved`).
        self.nodes[node].invalidate_blocking_cache();
        // `AnywhereValidatedBlocking.validationInfoChanged`: a change at or below
        // the last-validated frontier rewinds it so re-validation reconsiders this
        // node (only consulted by the validated strategy).
        match self.last_validated_unchanged_node {
            Some(current) if id < self.nodes[current].node_id => {
                self.last_validated_unchanged_node = Some(node);
            }
            _ => {}
        }
    }

    /// `AnywhereValidatedBlocking.updateNodeChange`: lower `first_changed_node` to
    /// `node` if it is earlier, WITHOUT invalidating the cached blocking labels or
    /// setting `has_blocking_info_changed`. The validated strategy uses this for a
    /// core role-assertion add: the (concept-core-only) blocking signature is
    /// unaffected -- so the per-node recompute flag must stay clear, matching the
    /// validated direct checker's `assertionAdded(AtomicRole)` returning `null` and
    /// never setting `m_hasChangedForBlocking` -- but the reprocessing range must
    /// still extend to cover the endpoint.
    pub(crate) fn update_node_change(&mut self, node: NodeId) {
        let id = self.nodes[node].node_id;
        let is_lower = match self.first_changed_node {
            None => true,
            Some(current) => id < self.nodes[current].node_id,
        };
        if is_lower {
            self.first_changed_node = Some(node);
        }
    }

    /// `AnywhereValidatedBlocking.validationInfoChanged`: marks `node` as changed
    /// since the last block validation and rewinds the validation frontier so the
    /// next `validate_blocks` reconsiders it. Unlike `note_blocking_node_changed`
    /// it does NOT touch `first_changed_node` (that is `updateNodeChange`'s job)
    /// nor invalidate the cached blocking labels -- it is the pure
    /// `setHasChangedSinceValidation` + frontier-rewind that the validated strategy
    /// applies to a node's *parent* (concept changes) or the *other endpoint* (role
    /// changes) in addition to the directly-affected node.
    pub(crate) fn validation_info_changed(&mut self, node: NodeId) {
        let id = self.nodes[node].node_id;
        if let Some(current) = self.last_validated_unchanged_node {
            if id < self.nodes[current].node_id {
                self.last_validated_unchanged_node = Some(node);
            }
        }
        self.nodes[node].has_changed_since_validation = true;
    }

    /// `AnywhereValidatedBlocking.validationInfoChanged(node)`: applies
    /// [`validation_info_changed`](Self::validation_info_changed) to `node` itself
    /// when the validated strategy is active. A no-op for the exact anywhere/ancestor
    /// strategies, matching the fact that only `AnywhereValidatedBlocking.nodeStatusChanged`
    /// marks the node's own validation info changed (in addition to its parent).
    pub(crate) fn validation_info_changed_self(&mut self, node: NodeId) {
        if self.blocking_validator.is_some() {
            self.validation_info_changed(node);
        }
    }

    /// `AnywhereValidatedBlocking.validationInfoChanged(node.getParent())`: applies
    /// [`validation_info_changed`](Self::validation_info_changed) to `node`'s parent
    /// when the validated strategy is active. A no-op for the exact anywhere/ancestor
    /// strategies, matching the fact that only `AnywhereValidatedBlocking` overrides
    /// the assertion callbacks to also mark the parent.
    pub(crate) fn validation_info_changed_parent(&mut self, node: NodeId) {
        if self.blocking_validator.is_some() {
            if let Some(parent) = self.nodes[node].get_parent() {
                self.validation_info_changed(parent);
            }
        }
    }

    /// `AnywhereBlocking.nodeDestroyed`: drop the node from the blockers cache and,
    /// since tableau nodes are destroyed highest-id first, clear
    /// `first_changed_node` when it would point at (or past) the destroyed node.
    pub(crate) fn note_blocking_node_destroyed(&mut self, node: NodeId) {
        self.blockers_cache_remove(node);
        // `AnywhereValidatedBlocking.nodeDestroyed`: drop the node from the VALIDATED
        // blockers cache too. Under the validated strategy the anywhere cache above is
        // never populated, so without this the destroyed node's signature entry would
        // linger and could be returned as a (stale, since-reused) blocker candidate.
        if self.blocking_validator.is_some() {
            self.validated_cache_remove(node);
        }
        self.nodes[node].invalidate_blocking_cache();
        self.nodes[node].has_blocking_info_changed = false;
        if let Some(current) = self.first_changed_node {
            if self.nodes[current].node_id >= self.nodes[node].node_id {
                self.first_changed_node = None;
            }
        }
        // `AnywhereValidatedBlocking.nodeDestroyed`: rewind the validation frontier
        // to the destroyed node when it lies below the frontier, so re-validation
        // resumes from there (the destroyed node's tableau slot is the next one
        // reused, mirroring HermiT's node pooling).
        if let Some(current) = self.last_validated_unchanged_node {
            if self.nodes[node].node_id < self.nodes[current].node_id {
                self.last_validated_unchanged_node = Some(node);
            }
        }
    }

    fn blockers_cache_remove(&mut self, node: NodeId) {
        if let Some(signature) = self.blockers_cache_node_signature.remove(&node) {
            self.blockers_cache_by_signature.remove(&signature);
        }
    }

    fn blockers_cache_add(&mut self, node: NodeId, signature: CachedSignature) {
        self.blockers_cache_by_signature.insert(signature.clone(), node);
        self.blockers_cache_node_signature.insert(node, signature);
    }

    /// Ancestor blocking (`AncestorBlocking.computeBlocking` + `checkParentBlocking`):
    /// a node may be blocked only by one of its own ANCESTORS (walking up the
    /// parent chain) whose direct-blocking signature equals the node's, rather
    /// than by any earlier node anywhere. Otherwise identical to anywhere blocking
    /// (parent-propagated indirect blocking, the same cache short-circuit).
    fn compute_blocking_ancestor(&mut self) {
        let mut node = self.first_tableau_node;
        while let Some(current) = node {
            // `AncestorBlocking.computeBlocking` processes EVERY active node, with no
            // tree-node gate at the strategy level: the tree-node restriction is
            // enforced inside `isBlockedBy`/`checkParentBlocking`. An active non-tree
            // node whose parent is blocked is therefore still indirectly blocked.
            if self.nodes[current].is_active() {
                let parent = self.nodes[current].get_parent();
                if parent.is_none() {
                    self.nodes[current].set_blocked(None, false);
                } else if parent.is_some_and(|p| self.nodes[p].is_blocked()) {
                    self.nodes[current].set_blocked(parent, false);
                } else {
                    let signature = self.direct_signature(current);
                    if self.signature_is_cached(&signature) {
                        self.nodes[current].set_blocked(None, true);
                    } else {
                        // checkParentBlocking: walk up the ancestor chain for a
                        // node that directly blocks `current`.
                        let blocker = self.find_ancestor_blocker(current, &signature);
                        match blocker {
                            Some(b) => self.nodes[current].set_blocked(Some(b), true),
                            None => self.nodes[current].set_blocked(None, false),
                        }
                    }
                }
                // As in the anywhere pass: a node left unblocked that still carries
                // unprocessed existentials must be reconsidered by the expansion
                // walk, so pull the expansion cursor back to it.
                if !self.nodes[current].is_blocked()
                    && self.nodes[current].has_unprocessed_existentials()
                {
                    self.note_unprocessed_existential(current);
                }
            }
            node = self.nodes[current].next_tableau_node;
        }
    }

    /// `AncestorBlocking.checkParentBlocking`: the first unblocked tree-node
    /// ancestor whose direct-blocking signature equals `signature`. Mirrors
    /// `m_directBlockingChecker.isBlockedBy(blocker,node)` walking `getParent()`.
    fn find_ancestor_blocker(
        &mut self,
        node: NodeId,
        signature: &CachedSignature,
    ) -> Option<NodeId> {
        // `isBlockedBy` requires the blocked node itself to be a TREE_NODE, so a
        // non-tree node is never directly blocked by an ancestor.
        if self.nodes[node].get_node_type() != NodeType::TreeNode {
            return None;
        }
        let mut blocker = self.nodes[node].get_parent();
        while let Some(candidate) = blocker {
            // `isBlockedBy`: the blocker must merely be an unblocked TREE_NODE with
            // an equal signature -- it does NOT apply `canBeBlocker` (so no
            // active-node or parent-node-type gate, unlike the anywhere cache path).
            if !self.nodes[candidate].is_blocked()
                && self.nodes[candidate].get_node_type() == NodeType::TreeNode
                && &self.direct_signature(candidate) == signature
            {
                return Some(candidate);
            }
            blocker = self.nodes[candidate].get_parent();
        }
        None
    }

    /// Whether a signature cache is present and already contains `signature`.
    fn signature_is_cached(&self, signature: &CachedSignature) -> bool {
        self.blocking_signature_cache
            .as_ref()
            .is_some_and(|cache| cache.contains_signature(signature))
    }

    /// The direct-blocking signature of an eligible node, in the form the
    /// configured `DirectBlockingChecker` would compare: the single
    /// atomic-concept label, or the four-part pairwise tuple.
    fn direct_signature(&mut self, node: NodeId) -> CachedSignature {
        match self.direct_blocking_kind {
            DirectBlockingKind::Single => CachedSignature::Single(self.node_concept_label(node)),
            DirectBlockingKind::Pairwise => {
                let (n, p, fp, tp) = self.pairwise_signature(node);
                CachedSignature::Pairwise(n, p, fp, tp)
            }
        }
    }

    /// Port of the blocking strategies' `modelFound` hook over a
    /// signature cache. After a clash-free model is found, record the
    /// direct-blocking signature of every active, unblocked, blockable node so a
    /// later test can short-circuit blocking. A no-op when no cache is configured.
    pub fn cache_model_signatures(&mut self) {
        if self.blocking_signature_cache.is_none() {
            return;
        }
        let mut signatures: Vec<CachedSignature> = Vec::new();
        let mut node = self.first_tableau_node;
        while let Some(current) = node {
            if self.nodes[current].is_active()
                && !self.nodes[current].is_blocked()
                && self.can_participate_in_blocking(current)
            {
                signatures.push(self.direct_signature(current));
            }
            node = self.nodes[current].next_tableau_node;
        }
        if let Some(cache) = self.blocking_signature_cache.as_mut() {
            for signature in signatures {
                cache.add_signature(signature);
            }
        }
    }

    /// Validated anywhere blocking (`AnywhereValidatedBlocking` with
    /// `ValidatedSingleDirectBlockingChecker`): the candidate condition is the
    /// weaker *core* atomic-concept label (the concepts a node deterministically
    /// must have -- in particular the ∃-rule filler that created it, not the
    /// concepts later propagated onto it). Each candidate block is then
    /// validated, and rejected (the node unblocked) if it cannot be. The weaker
    /// candidate condition is what lets cyclic inverse-role ontologies block at a
    /// finite depth; the validator keeps it sound.
    /// Port of `AnywhereValidatedBlocking.computePreBlocking`: the cheap
    /// (candidate-only) pass run during normal expansion. From the first changed
    /// node it drops stale cache entries and re-blocks each node on its *core*
    /// signature, but -- once a validation has run -- only re-blocks a node whose
    /// own or candidate-blocker's validation state changed (or that keeps its
    /// previous blocker), which is what makes the pre-block/validate loop
    /// terminate. No block is validated here.
    fn compute_pre_blocking(&mut self) {
        let Some(start) = self.first_changed_node else {
            return;
        };
        let start_id = self.nodes[start].node_id;
        let mut node = Some(start);
        while let Some(current) = node {
            self.validated_cache_remove(current);
            node = self.nodes[current].next_tableau_node;
        }
        let mut node = Some(start);
        while let Some(current) = node {
            if self.nodes[current].is_active() && self.can_participate_in_blocking(current) {
                let recompute = self.nodes[current].has_blocking_info_changed
                    || !self.nodes[current].is_directly_blocked()
                    || match self.nodes[current].get_blocker() {
                        Some(b) => self.nodes[b].node_id >= start_id,
                        // A signature-cache block carries no concrete blocker node;
                        // HermiT's `SIGNATURE_CACHE_BLOCKER` sentinel has nodeID -1,
                        // so this term is false (a real first-changed node has id >= 0).
                        None => -1 >= start_id,
                    };
                if recompute {
                    let parent = self.nodes[current].get_parent();
                    if parent.is_none() {
                        self.nodes[current].set_blocked(None, false);
                    } else if parent.is_some_and(|p| self.nodes[p].is_blocked()) {
                        self.nodes[current].set_blocked(parent, false);
                    } else {
                        let signature = self.validated_block_signature(current);
                        let blocker = if self.last_validated_unchanged_node.is_none() {
                            self.validated_get_blocker(current, &signature)
                        } else {
                            // After a validation, only re-block on a change.
                            let previous_blocker = self.nodes[current].get_blocker();
                            let node_modified =
                                self.nodes[current].has_changed_since_validation;
                            let mut chosen = None;
                            for possible in self.validated_get_possible_blockers(&signature) {
                                if node_modified
                                    || self.nodes[possible].has_changed_since_validation
                                    || previous_blocker == Some(possible)
                                {
                                    chosen = Some(possible);
                                    break;
                                }
                            }
                            chosen
                        };
                        self.nodes[current].set_blocked(blocker, blocker.is_some());
                    }
                }
                if !self.nodes[current].is_blocked() {
                    let signature = self.validated_block_signature(current);
                    self.validated_cache_add(current, signature);
                }
            }
            self.nodes[current].has_blocking_info_changed = false;
            node = self.nodes[current].next_tableau_node;
        }
        self.first_changed_node = None;
    }

    /// Port of `AnywhereValidatedBlocking.validateBlocks`: the final-chance pass.
    /// Resuming from the last validated node, it validates each directly blocked
    /// node whose validation state changed (trying the existing blocker, then the
    /// other same-core candidates), unblocks those that cannot be validated, and
    /// records the lowest invalidly blocked node as the next `first_changed_node`
    /// so expansion resumes there.
    fn validate_blocks(&mut self) {
        let validator = self.blocking_validator.take().expect("validator enabled");
        let first_validated = self.last_validated_unchanged_node.or(self.first_tableau_node);
        let mut node = first_validated;
        while let Some(current) = node {
            self.validated_cache_remove(current);
            node = self.nodes[current].next_tableau_node;
        }
        let mut first_invalidly_blocked: Option<NodeId> = None;
        let mut node = first_validated;
        while let Some(current) = node {
            node = self.nodes[current].next_tableau_node;
            if !self.nodes[current].is_active() {
                continue;
            }
            if self.nodes[current].is_blocked() {
                let directly = self.nodes[current].is_directly_blocked();
                let parent = self.nodes[current].get_parent();
                let parent_blocked = parent.is_some_and(|p| self.nodes[p].is_blocked());
                // Only re-validate a directly blocked node whose own/parent/blocker
                // validation state changed, or one whose parent is no longer blocked.
                let changed = directly
                    && (self.nodes[current].has_changed_since_validation
                        || parent.is_some_and(|p| self.nodes[p].has_changed_since_validation)
                        || self
                            .nodes[current]
                            .get_blocker()
                            .is_some_and(|b| self.nodes[b].has_changed_since_validation));
                if changed || !parent_blocked {
                    let current_blocker = self.nodes[current].get_blocker();
                    let mut valid_blocker: Option<NodeId> = None;
                    if directly
                        && current_blocker.is_some()
                        && validator.is_block_valid(self, current)
                    {
                        valid_blocker = current_blocker;
                    }
                    if valid_blocker.is_none() {
                        let signature = self.validated_block_signature(current);
                        for possible in self.validated_get_possible_blockers(&signature) {
                            if Some(possible) != current_blocker {
                                self.nodes[current].set_blocked(Some(possible), true);
                                // `BlockingValidator.blockerChanged`: drop the cached
                                // parent-constraint check so the new blocker's label
                                // is re-evaluated rather than reusing stale flags.
                                if let Some(p) = self.nodes[current].get_parent() {
                                    self.nodes[p].has_already_been_checked = false;
                                }
                                if validator.is_block_valid(self, current) {
                                    valid_blocker = Some(possible);
                                    break;
                                }
                            }
                        }
                    }
                    if valid_blocker.is_none()
                        && self.nodes[current].has_unprocessed_existentials()
                        && first_invalidly_blocked.is_none()
                    {
                        first_invalidly_blocked = Some(current);
                    }
                    self.nodes[current].set_blocked(valid_blocker, valid_blocker.is_some());
                }
            }
            self.last_validated_unchanged_node = Some(current);
            if !self.nodes[current].is_blocked() && self.can_participate_in_blocking(current) {
                let signature = self.validated_block_signature(current);
                self.validated_cache_add(current, signature);
            }
        }
        // Reset the per-node validation flags for the next pass.
        let mut node = first_validated;
        while let Some(current) = node {
            if self.nodes[current].is_active() {
                self.nodes[current].has_changed_since_validation = false;
                self.nodes[current].block_violates_parent_constraints = false;
                self.nodes[current].has_already_been_checked = false;
            }
            node = self.nodes[current].next_tableau_node;
        }
        // Resume expansion from the lowest invalidly blocked node next round.
        self.first_changed_node = first_invalidly_blocked;
        self.blocking_validator = Some(validator);
    }

    fn validated_cache_remove(&mut self, node: NodeId) {
        if let Some(signature) = self.validated_blockers_node_signature.remove(&node) {
            if let Some(bucket) = self.validated_blockers_by_signature.get_mut(&signature) {
                bucket.retain(|&n| n != node);
                if bucket.is_empty() {
                    self.validated_blockers_by_signature.remove(&signature);
                }
            }
        }
    }

    fn validated_cache_add(&mut self, node: NodeId, signature: ValidatedSignature) {
        self.validated_cache_remove(node);
        self.validated_blockers_by_signature
            .entry(signature.clone())
            .or_default()
            .push(node);
        self.validated_blockers_node_signature.insert(node, signature);
    }

    /// `ValidatedBlockersCache.getBlocker`: the node's current blocker when it is
    /// still a candidate with the given core signature ("don't change the blocker
    /// unnecessarily, the blocking validation code will change the blocker if
    /// necessary"), otherwise the representative (earliest) unblocked candidate.
    fn validated_get_blocker(
        &self,
        node: NodeId,
        signature: &ValidatedSignature,
    ) -> Option<NodeId> {
        let bucket = self.validated_blockers_by_signature.get(signature)?;
        if let Some(current) = self.nodes[node].get_blocker() {
            if bucket.contains(&current) {
                return Some(current);
            }
        }
        bucket.first().copied()
    }

    /// `ValidatedBlockersCache.getPossibleBlockers`: all unblocked candidates with
    /// the given core signature (validation tries each).
    fn validated_get_possible_blockers(&self, signature: &ValidatedSignature) -> Vec<NodeId> {
        self.validated_blockers_by_signature
            .get(signature)
            .cloned()
            .unwrap_or_default()
    }

    /// `canBeBlocker`/`canBeBlocked`: dispatches on the configured direct-blocking
    /// checker (SingleDirectBlockingChecker.java:64-69 vs
    /// PairWiseDirectBlockingChecker).
    ///
    /// * `Single`   -- the node must be an active `TREE_NODE`; no parent gate
    ///   (Java `SingleDirectBlockingChecker.canBeBlocked` checks only
    ///   `node.getNodeType()==NodeType.TREE_NODE`).
    /// * `Pairwise` -- additionally requires the parent to be a tree or graph node,
    ///   because the pairwise signature reads the parent label and both edge labels;
    ///   a node without such a parent has no well-defined pairwise signature.
    fn can_participate_in_blocking(&self, node: NodeId) -> bool {
        if !self.nodes[node].is_active()
            || self.nodes[node].get_node_type() != NodeType::TreeNode
        {
            return false;
        }
        let parent_is_tree_or_graph = || {
            matches!(
                self.nodes[node].get_parent(),
                Some(parent)
                    if matches!(
                        self.nodes[parent].get_node_type(),
                        NodeType::TreeNode | NodeType::GraphNode
                    )
            )
        };
        // The validated direct-blocking checkers
        // (`ValidatedSingleDirectBlockingChecker` /
        // `ValidatedPairwiseDirectBlockingChecker`, used by the core strategies)
        // gate eligibility on `!hasInverses || parent ∈ {tree, graph}` for both
        // the single and pairwise label variants.
        if matches!(
            self.blocking_strategy_kind,
            BlockingStrategyKind::ValidatedCore { .. }
        ) {
            return !self.blocking_has_inverses || parent_is_tree_or_graph();
        }
        // SingleDirectBlockingChecker.canBeBlocked/canBeBlocker: just TREE_NODE.
        if self.direct_blocking_kind == DirectBlockingKind::Single {
            return true;
        }
        // PairWiseDirectBlockingChecker: parent must be tree or graph node.
        parent_is_tree_or_graph()
    }

    /// The pairwise blocking signature of an eligible node (parent guaranteed).
    fn pairwise_signature(&mut self, node: NodeId) -> PairwiseSignature {
        let parent = self.nodes[node].get_parent().expect("eligible node has a parent");
        let node_label = self.node_concept_label(node);
        let parent_label = self.node_concept_label(parent);
        let from_parent = self.from_parent_label(node, parent);
        let to_parent = self.to_parent_label(node, parent);
        (node_label, parent_label, from_parent, to_parent)
    }

    /// The parent->node edge role label, cached on the node
    /// (`PairWiseBlockingObject.getFromParentLabel`).
    fn from_parent_label(&mut self, node: NodeId, parent: NodeId) -> Vec<AtomicRole> {
        if self.nodes[node].blocking_from_parent_cache.is_none() {
            let label = self.scan_edge_label(parent, node);
            self.nodes[node].blocking_from_parent_cache = Some(label);
        }
        self.nodes[node].blocking_from_parent_cache.clone().unwrap()
    }

    /// The node->parent edge role label, cached on the node
    /// (`PairWiseBlockingObject.getToParentLabel`).
    fn to_parent_label(&mut self, node: NodeId, parent: NodeId) -> Vec<AtomicRole> {
        if self.nodes[node].blocking_to_parent_cache.is_none() {
            let label = self.scan_edge_label(node, parent);
            self.nodes[node].blocking_to_parent_cache = Some(label);
        }
        self.nodes[node].blocking_to_parent_cache.clone().unwrap()
    }

    /// The set of *core* atomic concepts on `node`: those asserted with the core
    /// flag (the concepts the node deterministically must have, including the
    /// ∃-rule filler that created it), used as the validated-blocking signature.
    fn node_core_concept_label(&mut self, node: NodeId) -> Vec<AtomicConcept> {
        if self.nodes[node].blocking_core_label_cache.is_none() {
            let label = self.scan_node_core_concept_label(node);
            self.nodes[node].blocking_core_label_cache = Some(label);
        }
        self.nodes[node].blocking_core_label_cache.clone().unwrap()
    }

    /// Reads the *core* atomic-concept label of `node` directly from the binary
    /// extension table.
    fn scan_node_core_concept_label(&self, node: NodeId) -> Vec<AtomicConcept> {
        let retrieval = self.create_binary_retrieval(
            [-1, 1],
            [None, Some(TableauObject::Node(node))],
            View::Total,
        );
        let mut label = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            if self.binary_extension_table.is_core(tuple_index) {
                if let TableauObject::Concept(crate::model::Concept::AtomicConcept(c)) =
                    self.binary_extension_table.get_tuple_object(tuple_index, 0)
                {
                    label.push(c.clone());
                }
            }
        }
        label.sort_unstable_by_key(|c| c.intern_ptr());
        label.dedup();
        label
    }

    /// The validated-blocking candidate signature: the node's own core label
    /// (`ValidatedSingleDirectBlockingChecker.isBlockedBy`), plus, under pairwise
    /// blocking, the parent's core label (`ValidatedPairwiseDirectBlockingChecker.
    /// isBlockedBy` also requires the parents' core labels to match).
    fn validated_block_signature(
        &mut self,
        node: NodeId,
    ) -> (Vec<AtomicConcept>, Option<Vec<AtomicConcept>>) {
        let own = self.node_core_concept_label(node);
        match self.direct_blocking_kind {
            DirectBlockingKind::Single => (own, None),
            DirectBlockingKind::Pairwise => {
                let parent = self
                    .nodes[node]
                    .get_parent()
                    .map(|p| self.node_core_concept_label(p))
                    .unwrap_or_default();
                (own, Some(parent))
            }
        }
    }

    /// The set of atomic concepts asserted on `node` (its blocking label),
    /// returned from the per-node cache and lazily refetched only when the cache
    /// was invalidated by a label change (`PairWiseBlockingObject.getAtomicConceptsLabel`).
    fn node_concept_label(&mut self, node: NodeId) -> Vec<AtomicConcept> {
        if self.nodes[node].blocking_label_cache.is_none() {
            let label = self.scan_node_concept_label(node);
            self.nodes[node].blocking_label_cache = Some(label);
        }
        self.nodes[node].blocking_label_cache.clone().unwrap()
    }

    /// Reads the atomic-concept label of `node` directly from the binary extension
    /// table (`fetchAtomicConceptsLabel`).
    fn scan_node_concept_label(&self, node: NodeId) -> Vec<AtomicConcept> {
        let retrieval =
            self.create_binary_retrieval([-1, 1], [None, Some(TableauObject::Node(node))], View::Total);
        let mut label = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            if let TableauObject::Concept(crate::model::Concept::AtomicConcept(c)) =
                self.binary_extension_table.get_tuple_object(tuple_index, 0)
            {
                label.push(c.clone());
            }
        }
        label.sort_unstable_by_key(|c| c.intern_ptr());
        label.dedup();
        label
    }

    /// The set of atomic roles `r` with `r(node_from, node_to)` asserted -- the
    /// directed edge label used in the pairwise signature.
    fn scan_edge_label(&self, node_from: NodeId, node_to: NodeId) -> Vec<AtomicRole> {
        let retrieval = self.create_ternary_retrieval(
            [-1, 1, 2],
            [
                None,
                Some(TableauObject::Node(node_from)),
                Some(TableauObject::Node(node_to)),
            ],
            View::Total,
        );
        let mut label = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            if let TableauObject::DLPredicate(DLPredicate::AtomicRole(r)) =
                self.ternary_extension_table.get_tuple_object(tuple_index, 0)
            {
                label.push(r.clone());
            }
        }
        label.sort_unstable_by_key(|c| c.intern_ptr());
        label.dedup();
        label
    }
}
