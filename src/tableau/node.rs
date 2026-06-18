// Port of org.semanticweb.HermiT.tableau.Node.
//
// A node in the tableau. Java `Node` objects reference each other and the
// `Tableau` directly; this port stores nodes in an arena owned by the `Tableau`
// and refers to them by `NodeId`. The back-reference `m_tableau` is therefore
// implicit, and the traversal methods (canonical node, ancestor checks, ...)
// live on `Tableau` where the arena is available. Pure per-node state and
// accessors live here.
#![allow(dead_code)]


use crate::model::{AtomicConcept, AtomicRole, ExistentialConcept};
use crate::tableau::dependency_set::PermanentDependencySet;
use crate::tableau::node_type::NodeType;

/// A handle to a node in the tableau's arena.
pub type NodeId = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeState {
    Active,
    Merged,
    Pruned,
}

pub struct Node {
    pub(crate) node_id: i32,
    pub(crate) node_state: Option<NodeState>,
    pub(crate) parent: Option<NodeId>,
    pub(crate) node_type: NodeType,
    pub(crate) tree_depth: i32,
    pub(crate) number_of_positive_atomic_concepts: i32,
    pub(crate) number_of_negated_atomic_concepts: i32,
    pub(crate) number_of_negated_role_assertions: i32,
    pub(crate) unprocessed_existentials: Vec<ExistentialConcept>,
    pub(crate) previous_tableau_node: Option<NodeId>,
    pub(crate) next_tableau_node: Option<NodeId>,
    pub(crate) previous_merged_or_pruned_node: Option<NodeId>,
    pub(crate) merged_into: Option<NodeId>,
    pub(crate) merged_into_dependency_set: Option<PermanentDependencySet>,
    /// The node that directly blocks this one, or `None` if unblocked / indirectly
    /// blocked. Java's `SIGNATURE_CACHE_BLOCKER` sentinel (Node.java:35) is encoded
    /// here as `blocker = None` with `directly_blocked = true`, set by
    /// `compute_blocking_anywhere` when `signature_is_cached` returns true.
    /// The `m_blockingObject` / `m_blockingCargo` fields (Node.java:161-185) are
    /// intentionally omitted: the Rust port does not implement a persistent
    /// BlockingSignatureCache and therefore needs no per-node cargo slot.
    pub(crate) blocker: Option<NodeId>,
    pub(crate) directly_blocked: bool,
    pub(crate) first_graph_occurrence_node: i32,
    /// Index of the next free node in the arena free list (when this slot is
    /// free), mirroring HermiT's `m_firstFreeNode` chain via `next_tableau_node`.
    pub(crate) next_free_node: Option<NodeId>,
    /// For a node representing a data constant, the constant it stands for.
    pub(crate) constant_value: Option<crate::model::Constant>,
    /// Validated-blocking state (`ValidatedBlockingObject`): whether this node's
    /// block has been found to violate its parent's constraints, and whether its
    /// parent has already been checked in the current validation pass.
    pub(crate) block_violates_parent_constraints: bool,
    pub(crate) has_already_been_checked: bool,
    /// `DirectBlockingChecker`'s `BlockingObject` cached labels: the node's atomic
    /// concept label, its core label (validated blocking), and the two directed
    /// parent-edge role labels. `None` means "not yet fetched / invalidated"; the
    /// label is lazily refetched from the extension tables and reused until the
    /// node's blocking info changes (`fetchAtomicConceptsLabel` etc.), so a
    /// blocking pass no longer rescans the tables for unchanged nodes.
    pub(crate) blocking_label_cache: Option<Vec<AtomicConcept>>,
    pub(crate) blocking_core_label_cache: Option<Vec<AtomicConcept>>,
    pub(crate) blocking_from_parent_cache: Option<Vec<AtomicRole>>,
    pub(crate) blocking_to_parent_cache: Option<Vec<AtomicRole>>,
    /// `BlockingObject.m_hasChanged` (`hasBlockingInfoChanged`): set when this
    /// node's blocking-relevant label changes, cleared once it is reprocessed in a
    /// blocking pass. Lets the incremental pass skip a directly blocked node whose
    /// own info has not changed and whose blocker lies below the changed range
    /// (`AnywhereBlocking.computeBlocking`'s recompute guard).
    pub(crate) has_blocking_info_changed: bool,
    /// The validated strategy's `hasChangedSinceValidation`: set when this node's
    /// validation-relevant state changes after the last `validateBlocks`, cleared
    /// at the end of that pass.
    pub(crate) has_changed_since_validation: bool,
}

impl Node {
    pub(crate) fn new_empty() -> Node {
        Node {
            node_id: -1,
            node_state: None,
            parent: None,
            node_type: NodeType::TreeNode,
            tree_depth: 0,
            number_of_positive_atomic_concepts: 0,
            number_of_negated_atomic_concepts: 0,
            number_of_negated_role_assertions: 0,
            unprocessed_existentials: Vec::new(),
            previous_tableau_node: None,
            next_tableau_node: None,
            previous_merged_or_pruned_node: None,
            merged_into: None,
            merged_into_dependency_set: None,
            blocker: None,
            directly_blocked: false,
            first_graph_occurrence_node: -1,
            next_free_node: None,
            constant_value: None,
            block_violates_parent_constraints: false,
            has_already_been_checked: false,
            blocking_label_cache: None,
            blocking_core_label_cache: None,
            blocking_from_parent_cache: None,
            blocking_to_parent_cache: None,
            has_blocking_info_changed: false,
            has_changed_since_validation: false,
        }
    }

    /// `BlockingObject` invalidation: drop the cached blocking labels and mark the
    /// node's blocking info changed, so the next blocking pass refetches its
    /// label and reconsiders its block (`DirectBlockingChecker.assertionAdded`/
    /// `assertionRemoved` setting `m_hasChanged` and nulling the cached sets).
    pub(crate) fn invalidate_blocking_cache(&mut self) {
        self.blocking_label_cache = None;
        self.blocking_core_label_cache = None;
        self.blocking_from_parent_cache = None;
        self.blocking_to_parent_cache = None;
        self.has_blocking_info_changed = true;
        self.has_changed_since_validation = true;
    }

    pub fn constant_value(&self) -> Option<&crate::model::Constant> {
        self.constant_value.as_ref()
    }

    pub fn get_node_id(&self) -> i32 {
        self.node_id
    }
    pub fn get_parent(&self) -> Option<NodeId> {
        self.parent
    }
    pub fn is_root_node(&self) -> bool {
        self.parent.is_none()
    }
    pub fn get_node_type(&self) -> NodeType {
        self.node_type
    }
    pub fn get_tree_depth(&self) -> i32 {
        self.tree_depth
    }
    pub fn is_blocked(&self) -> bool {
        // Java `Node.isBlocked()` is `m_blocker != null`. A signature-cache
        // block uses the non-null `SIGNATURE_CACHE_BLOCKER` sentinel with
        // `m_directlyBlocked == true`; this port models that sentinel as
        // `(blocker = None, directly_blocked = true)`, so a cache block must
        // still count as blocked. Because Java's `m_directlyBlocked` always
        // implies a non-null blocker, `blocker.is_some() || directly_blocked`
        // matches `m_blocker != null` in every case.
        self.blocker.is_some() || self.directly_blocked
    }
    pub fn is_directly_blocked(&self) -> bool {
        self.directly_blocked
    }
    pub fn is_indirectly_blocked(&self) -> bool {
        self.blocker.is_some() && !self.directly_blocked
    }
    pub fn get_blocker(&self) -> Option<NodeId> {
        self.blocker
    }
    pub fn set_blocked(&mut self, blocker: Option<NodeId>, directly_blocked: bool) {
        self.blocker = blocker;
        self.directly_blocked = directly_blocked;
    }
    pub fn get_number_of_positive_atomic_concepts(&self) -> i32 {
        self.number_of_positive_atomic_concepts
    }
    pub fn is_active(&self) -> bool {
        self.node_state == Some(NodeState::Active)
    }
    pub fn is_merged(&self) -> bool {
        self.node_state == Some(NodeState::Merged)
    }
    pub fn get_merged_into(&self) -> Option<NodeId> {
        self.merged_into
    }
    pub fn get_merged_into_dependency_set(&self) -> Option<&PermanentDependencySet> {
        self.merged_into_dependency_set.as_ref()
    }
    pub fn is_pruned(&self) -> bool {
        self.node_state == Some(NodeState::Pruned)
    }
    pub fn get_previous_tableau_node(&self) -> Option<NodeId> {
        self.previous_tableau_node
    }
    pub fn get_next_tableau_node(&self) -> Option<NodeId> {
        self.next_tableau_node
    }
    pub fn has_unprocessed_existentials(&self) -> bool {
        !self.unprocessed_existentials.is_empty()
    }
    pub fn get_some_unprocessed_existential(&self) -> Option<&ExistentialConcept> {
        self.unprocessed_existentials.last()
    }
    pub fn get_unprocessed_existentials(&self) -> &[ExistentialConcept] {
        &self.unprocessed_existentials
    }
}

// Java Node.toString(): return String.valueOf(m_nodeID);
impl std::fmt::Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.node_id)
    }
}

#[cfg(test)]
mod tests {
    use super::Node;

    // Java's signature-cache block uses the non-null `SIGNATURE_CACHE_BLOCKER`
    // sentinel with `directlyBlocked = true`, so `isBlocked()` is true. This port
    // encodes that sentinel as `(blocker = None, directly_blocked = true)`, so a
    // cache-blocked node must still report `is_blocked() == true` while remaining
    // directly (not indirectly) blocked.
    #[test]
    fn signature_cache_block_counts_as_blocked() {
        let mut node = Node::new_empty();

        // Unblocked.
        node.set_blocked(None, false);
        assert!(!node.is_blocked());
        assert!(!node.is_directly_blocked());
        assert!(!node.is_indirectly_blocked());

        // Signature-cache block (Java SIGNATURE_CACHE_BLOCKER sentinel).
        node.set_blocked(None, true);
        assert!(node.is_blocked(), "cache-blocked node must be blocked");
        assert!(node.is_directly_blocked());
        assert!(!node.is_indirectly_blocked());

        // Directly blocked by a concrete node.
        node.set_blocked(Some(0), true);
        assert!(node.is_blocked());
        assert!(node.is_directly_blocked());
        assert!(!node.is_indirectly_blocked());

        // Indirectly blocked (parent blocked).
        node.set_blocked(Some(0), false);
        assert!(node.is_blocked());
        assert!(!node.is_directly_blocked());
        assert!(node.is_indirectly_blocked());
    }
}
