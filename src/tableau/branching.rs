// Port of the disjunction-branching and backtracking machinery:
// org.semanticweb.HermiT.tableau.{GroundDisjunction, BranchingPoint,
// DisjunctionBranchingPoint} and the Tableau branching/backtracking methods.
//
// When a ground disjunction is neither pruned nor already satisfied, a branching
// point is pushed and its first disjunct is added (tagged with the branching
// point in its dependency set). On a clash, dependency-directed backtracking
// jumps back to the maximum branching point in the clash dependency set,
// restoring all state (extension tables, nodes, merges/prunes, ground
// disjunctions, existentials, dependency sets), and the next disjunct is tried.
//
// AnnotatedEquality disjuncts (the at-most rule) are applied via
// `apply_annotated_equality`: `canForgetAnnotation` chooses a direct merge, else
// the nominal-introduction (NI) rule fires, with a `NominalIntroductionBranching
// Point` choosing among the `n` candidate NI roots for an at-most `n>1`.
#![allow(dead_code)]

use crate::model::{AnnotatedEquality, AtLeastConcept, AtomicConcept, Concept, DLPredicate};
use crate::tableau::dependency_set::{DependencySet, DependencySetOps, PermanentDependencySet};
use crate::tableau::hyperresolution::predicate_to_stored_label;
use crate::tableau::node::NodeId;
use crate::tableau::node::NodeState;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;

pub struct GroundDisjunctionData {
    pub(crate) header_index: usize,
    pub(crate) arguments: Vec<NodeId>,
    pub(crate) is_core: Vec<bool>,
    pub(crate) dependency_set: PermanentDependencySet,
    pub(crate) previous: Option<usize>,
    pub(crate) next: Option<usize>,
}

#[derive(Clone)]
pub struct BranchingPointData {
    pub(crate) level: i32,
    pub(crate) last_tableau_node: Option<NodeId>,
    pub(crate) last_merged_or_pruned_node: Option<NodeId>,
    pub(crate) first_ground_disjunction: Option<usize>,
    pub(crate) first_unprocessed_ground_disjunction: Option<usize>,
    pub(crate) ground_disjunction: usize,
    pub(crate) sorted_disjunct_indexes: Vec<usize>,
    pub(crate) current_index: usize,
    /// Set for a `NominalIntroductionBranchingPoint` (the at-most `n>1`-over-
    /// nominals NN rule); `None` for an ordinary disjunction branching point.
    pub(crate) nominal_introduction: Option<NIBranchingData>,
    /// Set for an `IndividualReuseStrategy.IndividualReuseBranchingPoint` (the
    /// witness-reuse third branching-point kind); `None` otherwise. On a clash
    /// that depends on the reuse decision, `startNextChoice` retries by creating
    /// a FRESH witness node instead of reusing one.
    pub(crate) reuse: Option<ReuseBranchingData>,
}

/// State of an `IndividualReuseStrategy.IndividualReuseBranchingPoint`: the
/// existential `>=1 r.C` whose witness was reused (either the parent, in the
/// `try_parent_reuse` case, or the per-concept representative node, in the
/// `expand_with_model_reuse` case) on the node `for_node`. On backtracking the
/// reuse is abandoned and a fresh tree successor is created instead.
#[derive(Clone)]
pub struct ReuseBranchingData {
    pub(crate) existential: AtLeastConcept,
    pub(crate) for_node: NodeId,
    /// Whether the reused witness was the parent (`try_parent_reuse`); when this
    /// is `false` the reuse was via the per-concept representative
    /// (`expand_with_model_reuse`) and the target concept is removed from the
    /// "reuse this run" set on retry.
    pub(crate) was_parent_reuse: bool,
}

/// State of a `NominalIntroductionBranchingPoint`: the choice tries the target
/// node against each of the `n` candidate NI root nodes in turn.
#[derive(Clone)]
pub struct NIBranchingData {
    pub(crate) root_node: NodeId,
    pub(crate) ni_target_node: NodeId,
    pub(crate) other_node: NodeId,
    pub(crate) annotated_equality: AnnotatedEquality,
    pub(crate) current_root_node: i32,
}

/// A buffered derived `AnnotatedEquality` (cardinality `> 1`) awaiting the
/// nominal-introduction rule. Mirrors a row of Java's
/// `NominalIntroductionManager.m_annotatedEqualities` tuple table
/// `[annotatedEquality, node0, node1, node2, permanentDependencySet]`.
#[derive(Clone)]
pub struct BufferedAnnotatedEquality {
    pub(crate) annotated_equality: AnnotatedEquality,
    pub(crate) node0: NodeId,
    pub(crate) node1: NodeId,
    pub(crate) node2: NodeId,
    pub(crate) dependency_set: PermanentDependencySet,
}

impl Tableau {
    // -- Ground disjunctions -------------------------------------------------

    /// Creates a ground disjunction and adds it unless it is already satisfied.
    pub fn derive_disjunction(
        &mut self,
        header_predicates: Vec<DLPredicate>,
        arguments: Vec<NodeId>,
        is_core: Vec<bool>,
        dependency_set: DependencySet,
    ) {
        let permanent = self.dependency_set_factory.get_permanent(&dependency_set);
        self.dependency_set_factory.add_usage(&permanent);
        let header_index = self.ground_disjunction_header_manager.get(header_predicates);
        let gd = GroundDisjunctionData {
            header_index,
            arguments,
            is_core,
            dependency_set: permanent.clone(),
            previous: None,
            next: None,
        };
        let gd_index = self.ground_disjunctions.len();
        self.ground_disjunctions.push(Some(gd));
        if self.ground_disjunction_satisfied(gd_index) {
            self.ground_disjunctions[gd_index] = None;
        } else {
            self.add_ground_disjunction(gd_index);
        }
    }

    fn add_ground_disjunction(&mut self, gd_index: usize) {
        let first = self.first_ground_disjunction;
        {
            let gd = self.ground_disjunctions[gd_index].as_mut().unwrap();
            gd.next = first;
            gd.previous = None;
        }
        if let Some(first) = first {
            self.ground_disjunctions[first].as_mut().unwrap().previous = Some(gd_index);
        }
        self.first_ground_disjunction = Some(gd_index);
        if self.first_unprocessed_ground_disjunction.is_none() {
            self.first_unprocessed_ground_disjunction = Some(gd_index);
        }
        self.monitor_event(|m| m.ground_disjunction_derived()); // groundDisjunctionDerived
    }

    fn destroy_ground_disjunction(&mut self, gd_index: usize) {
        if let Some(gd) = self.ground_disjunctions[gd_index].take() {
            self.dependency_set_factory.remove_usage(&gd.dependency_set);
        }
    }

    fn ground_disjunction_is_pruned(&self, gd_index: usize) -> bool {
        let gd = self.ground_disjunctions[gd_index].as_ref().unwrap();
        gd.arguments
            .iter()
            .any(|&n| self.nodes[n].node_state == Some(NodeState::Pruned))
    }

    fn ground_disjunction_satisfied(&self, gd_index: usize) -> bool {
        let gd = self.ground_disjunctions[gd_index].as_ref().unwrap();
        let header = self.ground_disjunction_header_manager.header(gd.header_index);
        let num_disjuncts = header.dl_predicates().len();
        for disjunct_index in 0..num_disjuncts {
            let predicate = header.dl_predicates()[disjunct_index].clone();
            let start = header.disjunct_start(disjunct_index);
            match predicate.arity() {
                1 => {
                    let arg = self.get_canonical_node(gd.arguments[start]);
                    if self.contains_assertion_unary(&predicate, arg) {
                        return true;
                    }
                }
                2 => {
                    let a0 = self.get_canonical_node(gd.arguments[start]);
                    let a1 = self.get_canonical_node(gd.arguments[start + 1]);
                    if self.contains_assertion_binary(&predicate, a0, a1) {
                        return true;
                    }
                }
                3 => {
                    // Port of `GroundDisjunction.isSatisfied` /
                    // `ExtensionManager.containsAnnotatedEquality`: an
                    // AnnotatedEquality disjunct is satisfied iff its annotation
                    // can be forgotten AND the two equated nodes are already the
                    // same node.
                    if matches!(predicate, DLPredicate::AnnotatedEquality(_)) {
                        let a0 = self.get_canonical_node(gd.arguments[start]);
                        let a1 = self.get_canonical_node(gd.arguments[start + 1]);
                        let a2 = self.get_canonical_node(gd.arguments[start + 2]);
                        if self.can_forget_annotation(a0, a1, a2) && a0 == a1 {
                            return true;
                        }
                    } else {
                        panic!("Invalid arity of DL-predicate.");
                    }
                }
                _ => panic!("Invalid arity of DL-predicate."),
            }
        }
        false
    }

    pub(crate) fn contains_assertion_unary(&self, predicate: &DLPredicate, node: NodeId) -> bool {
        if matches!(predicate, DLPredicate::AtomicConcept(c) if c == AtomicConcept::thing()) {
            return true;
        }
        let label = predicate_to_stored_label(predicate);
        let tuple = [label, TableauObject::Node(node)];
        self.binary_extension_table.get_tuple_index(&tuple) != -1 && self.nodes[node].is_active()
    }

    pub(crate) fn contains_assertion_binary(
        &self,
        predicate: &DLPredicate,
        node0: NodeId,
        node1: NodeId,
    ) -> bool {
        if matches!(predicate, DLPredicate::Equality) {
            return node0 == node1;
        }
        let tuple = [
            TableauObject::DLPredicate(predicate.clone()),
            TableauObject::Node(node0),
            TableauObject::Node(node1),
        ];
        self.ternary_extension_table.get_tuple_index(&tuple) != -1
            && self.nodes[node0].is_active()
            && self.nodes[node1].is_active()
    }

    fn add_disjunct_to_tableau(
        &mut self,
        gd_index: usize,
        disjunct_index: usize,
        dependency_set: DependencySet,
    ) -> bool {
        let (predicate, start, is_core, arguments) = {
            let gd = self.ground_disjunctions[gd_index].as_ref().unwrap();
            let header = self.ground_disjunction_header_manager.header(gd.header_index);
            (
                header.dl_predicates()[disjunct_index].clone(),
                header.disjunct_start(disjunct_index),
                gd.is_core[disjunct_index],
                gd.arguments.clone(),
            )
        };
        match predicate.arity() {
            1 => {
                let raw = arguments[start];
                let node = self.get_canonical_node(raw);
                let dep = self.add_canonical_node_dependency_set(raw, &dependency_set);
                self.add_unary_from_predicate(predicate, node, &DependencySet::Permanent(dep), is_core)
            }
            2 => {
                let raw0 = arguments[start];
                let raw1 = arguments[start + 1];
                let node0 = self.get_canonical_node(raw0);
                let node1 = self.get_canonical_node(raw1);
                let dep = self.add_canonical_node_dependency_set(raw0, &dependency_set);
                let dep = self.add_canonical_node_dependency_set(raw1, &DependencySet::Permanent(dep));
                self.add_binary_from_predicate(
                    predicate,
                    node0,
                    node1,
                    &DependencySet::Permanent(dep),
                    is_core,
                )
            }
            3 => {
                if let DLPredicate::AnnotatedEquality(annotated_equality) = predicate {
                    let raw0 = arguments[start];
                    let raw1 = arguments[start + 1];
                    let raw2 = arguments[start + 2];
                    let node0 = self.get_canonical_node(raw0);
                    let node1 = self.get_canonical_node(raw1);
                    let node2 = self.get_canonical_node(raw2);
                    let dep = self.add_canonical_node_dependency_set(raw0, &dependency_set);
                    let dep =
                        self.add_canonical_node_dependency_set(raw1, &DependencySet::Permanent(dep));
                    let dep =
                        self.add_canonical_node_dependency_set(raw2, &DependencySet::Permanent(dep));
                    // Java's `GroundDisjunction.addDisjunctToTableau` routes an
                    // annotated-equality disjunct through
                    // `ExtensionManager.addAnnotatedEquality`, i.e. the
                    // nominal-introduction dispatcher: it checks activity, may
                    // forget the annotation (direct merge), applies the NI rule
                    // immediately for a `<= 1` annotation, and buffers a
                    // cardinality-`> 1` annotation for `process_annotated_equalities`
                    // rather than firing it (and its branching point) nested inside
                    // disjunction processing.
                    self.add_annotated_equality(
                        &annotated_equality,
                        node0,
                        node1,
                        node2,
                        &DependencySet::Permanent(dep),
                    )
                } else {
                    panic!("Unsupported predicate arity.");
                }
            }
            _ => panic!("Unsupported predicate arity."),
        }
    }

    /// Port of `NominalIntroductionManager.canForgetAnnotation`: the annotation
    /// can be dropped (so the two successors may simply be merged) unless the
    /// owner `node2` is a root that is not the parent of both successors and
    /// neither successor is itself a root.
    fn can_forget_annotation(&self, node0: NodeId, node1: NodeId, node2: NodeId) -> bool {
        self.nodes[node0].is_root_node()
            || self.nodes[node1].is_root_node()
            || !self.nodes[node2].is_root_node()
            || (self.is_parent_of(node2, node0) && self.is_parent_of(node2, node1))
    }

    fn is_parent_of(&self, parent: NodeId, child: NodeId) -> bool {
        self.nodes[child].get_parent() == Some(parent)
    }

    /// Port of `NominalIntroductionManager.getNIRootFor`: the *stable* NI root
    /// node for `(root_node, annotated_equality, number)`, created on demand.
    ///
    /// As in Java, a cached node is returned **unconditionally** -- even if it has
    /// since been merged away (is inactive). The callers are responsible for
    /// canonicalizing a merged root (`get_canonical_node`) and folding in its merge
    /// dependency set (`add_canonical_node_dependency_set`). This preserves the
    /// "exactly one NI root per key" invariant the at-most-cardinality reasoning
    /// relies on; re-creating a fresh node here would let the NI rule introduce more
    /// distinct roots than the `<=n` restriction intends and miss the clash.
    fn ni_root_for(
        &mut self,
        dependency_set: &DependencySet,
        root_node: NodeId,
        annotated_equality: &AnnotatedEquality,
        number: i32,
    ) -> NodeId {
        let key = (root_node, annotated_equality.clone(), number);
        if let Some(&existing) = self.ni_roots.get(&key) {
            return existing;
        }
        let new_root = self.create_new_ni_node(dependency_set);
        self.ni_roots.insert(key.clone(), new_root);
        // Record insertion order so backtracking can drop entries created after a
        // branching point (mirrors appending to Java's `m_newRootNodesTable`).
        self.ni_roots_log.push(key);
        new_root
    }

    /// The Java `applyNIRule`/`startNextChoice` recovery for an NI root returned by
    /// `ni_root_for` that has since been merged: switch to its canonical survivor
    /// and fold the merge chain's dependency set into `dep`.
    fn canonicalize_ni_root(
        &mut self,
        new_root_node: NodeId,
        dep: &DependencySet,
    ) -> (NodeId, DependencySet) {
        if self.nodes[new_root_node].is_active() {
            (new_root_node, dep.clone())
        } else {
            let folded = self.add_canonical_node_dependency_set(new_root_node, dep);
            (
                self.get_canonical_node(new_root_node),
                DependencySet::Permanent(folded),
            )
        }
    }

    /// Port of `NominalIntroductionManager.addAnnotatedEquality` (the entry
    /// point called by the extension manager when an `AnnotatedEquality` fact is
    /// derived). Java dispatches in four ways
    /// (`NominalIntroductionManager.java:111-128`):
    /// - all three raw nodes must be active, else no-op;
    /// - `canForgetAnnotation` (on the raw nodes) -> merge the two raw nodes;
    /// - cardinality `== 1` -> apply the NI rule **immediately**;
    /// - cardinality `> 1` -> **buffer** the equality (with a permanent
    ///   dependency set) and defer the NI rule + its branching point to
    ///   `process_annotated_equalities`, run after deterministic saturation.
    ///
    /// Applying the `> 1` case eagerly here would interleave the nondeterministic
    /// NI branching into hyperresolution, changing the search shape and the
    /// branching-point levels that backtracking targets.
    pub(crate) fn add_annotated_equality(
        &mut self,
        annotated_equality: &AnnotatedEquality,
        raw0: NodeId,
        raw1: NodeId,
        raw2: NodeId,
        dependency_set: &DependencySet,
    ) -> bool {
        // `NominalIntroductionManager.java:112`: the raw nodes must all be active
        // (a merged-but-not-pruned node makes this rule a no-op until it is
        // re-derived for the canonical node).
        if !self.nodes[raw0].is_active()
            || !self.nodes[raw1].is_active()
            || !self.nodes[raw2].is_active()
        {
            return false;
        }
        // `:114`: forget the annotation -> merge the two raw nodes directly.
        if self.can_forget_annotation(raw0, raw1, raw2) {
            return self.merge_nodes(raw0, raw1, dependency_set);
        }
        // `:116`: a functional/`<= 1` annotation is deterministic, applied now.
        if annotated_equality.cardinality() == 1 {
            return self.apply_annotated_equality(annotated_equality, raw0, raw1, raw2, dependency_set);
        }
        // `:118-127`: cardinality `> 1` is nondeterministic -- buffer it and let
        // `process_annotated_equalities` fire the NI rule + branching point later.
        let permanent = self.dependency_set_factory.get_permanent(dependency_set);
        self.dependency_set_factory.add_usage(&permanent);
        self.annotated_equalities.push(BufferedAnnotatedEquality {
            annotated_equality: annotated_equality.clone(),
            node0: raw0,
            node1: raw1,
            node2: raw2,
            dependency_set: permanent,
        });
        true
    }

    /// Port of `NominalIntroductionManager.processAnnotatedEqualities`
    /// (`:92-107`): drain the buffered cardinality-`> 1` annotated equalities
    /// from the read cursor, firing the NI rule (`apply_annotated_equality`) for
    /// each. Returns `true` if any fired. Called at the top of `do_iteration` and
    /// after each propagate-loop body (Java `Tableau.doIteration:412,426`).
    pub(crate) fn process_annotated_equalities(&mut self) -> bool {
        let mut result = false;
        while self.first_unprocessed_annotated_equality < self.annotated_equalities.len() {
            let buffered =
                self.annotated_equalities[self.first_unprocessed_annotated_equality].clone();
            self.first_unprocessed_annotated_equality += 1;
            let dependency_set = DependencySet::Permanent(buffered.dependency_set);
            if self.apply_annotated_equality(
                &buffered.annotated_equality,
                buffered.node0,
                buffered.node1,
                buffered.node2,
                &dependency_set,
            ) {
                result = true;
            }
            self.note_interrupt();
        }
        result
    }

    /// Port of `NominalIntroductionManager.applyNIRule` (`:130-173`): canonicalize
    /// the three nodes, re-check `canForgetAnnotation`, and either merge directly
    /// or fire the nominal-introduction (NI) rule, merging the target node into a
    /// fresh NI root node.
    ///
    /// For an at-most `n > 1` over nominals the choice among the `n` candidate
    /// NI roots is made non-deterministically: a `NominalIntroductionBranching
    /// Point` is pushed and `ni_start_next_choice` advances to the next NI root
    /// on backtracking.
    pub(crate) fn apply_annotated_equality(
        &mut self,
        annotated_equality: &AnnotatedEquality,
        raw0: NodeId,
        raw1: NodeId,
        raw2: NodeId,
        dependency_set: &DependencySet,
    ) -> bool {
        // Java tests `isPruned()` on the raw input nodes *before* canonicalizing
        // (a canonical survivor is never pruned, so checking the canonical nodes
        // would defeat the guard for a buffered equality whose raw node was
        // merged by an intervening rule).
        if self.nodes[raw0].is_pruned()
            || self.nodes[raw1].is_pruned()
            || self.nodes[raw2].is_pruned()
        {
            return false;
        }
        let node0 = self.get_canonical_node(raw0);
        let node1 = self.get_canonical_node(raw1);
        let node2 = self.get_canonical_node(raw2);
        let dep = self.add_canonical_node_dependency_set(raw0, dependency_set);
        let dep = self.add_canonical_node_dependency_set(raw1, &DependencySet::Permanent(dep));
        let dep = self.add_canonical_node_dependency_set(raw2, &DependencySet::Permanent(dep));
        let dep = DependencySet::Permanent(dep);

        if self.can_forget_annotation(node0, node1, node2) {
            return self.merge_nodes(node0, node1, &dep);
        }

        // The nominal-introduction rule. The target node is merged into a fresh
        // NI root node; for an at-most `n>1` restriction the choice over the `n`
        // candidate NI roots is a NominalIntroductionBranchingPoint.
        let (ni_target_node, other_node) =
            if !self.nodes[node0].is_root_node() && !self.is_parent_of(node2, node0) {
                (node0, node1)
            } else {
                (node1, node0)
            };
        // `NominalIntroductionManager.applyNIRule`:153 — nominalIntorductionStarted,
        // fired after niTargetNode/otherNode are chosen and before the branching
        // point push.
        self.monitor_event(|m| m.nominal_introduction_started());
        let mut dep = dep;
        if annotated_equality.cardinality() > 1 {
            let branching_point = BranchingPointData {
                level: 0,
                last_tableau_node: self.last_tableau_node,
                last_merged_or_pruned_node: self.last_merged_or_pruned_node,
                first_ground_disjunction: self.first_ground_disjunction,
                first_unprocessed_ground_disjunction: self.first_unprocessed_ground_disjunction,
                ground_disjunction: usize::MAX,
                sorted_disjunct_indexes: Vec::new(),
                current_index: 0,
                nominal_introduction: Some(NIBranchingData {
                    root_node: node2,
                    ni_target_node,
                    other_node,
                    annotated_equality: annotated_equality.clone(),
                    current_root_node: 1,
                }),
                reuse: None,
            };
            self.push_branching_point(branching_point);
            let level = self.current_branching_point;
            let permanent = self.dependency_set_factory.add_branching_point(&dep, level);
            dep = DependencySet::Permanent(permanent);
        }
        let new_root_node = self.ni_root_for(&dep, node2, annotated_equality, 1);
        let (new_root_node, dep) = self.canonicalize_ni_root(new_root_node, &dep);
        // Java `applyNIRule` line 165: `m_mergingManager.mergeNodes(niTargetNode,
        // newRootNode, dependencySet);`. Here `ni_target_node` is one of `node0`/`node1`,
        // already canonicalized above (cf. Java lines 136-138), so no extra fold.
        self.merge_nodes(ni_target_node, new_root_node, &dep);
        // Java `applyNIRule` lines 166-168:
        //   if (!otherNode.isPruned()) {
        //       dependencySet=otherNode.addCanonicalNodeDependencySet(dependencySet);
        //       m_mergingManager.mergeNodes(otherNode.getCanonicalNode(),newRootNode,dependencySet);
        //   }
        // `other_node` is already canonical at this point (it is `node0`/`node1`
        // canonicalized above), so this fold is a no-op here -- but mirror Java
        // line 167 exactly for faithfulness (a no-op fold is harmless).
        if !self.nodes[other_node].is_pruned() {
            let folded = self.add_canonical_node_dependency_set(other_node, &dep);
            let dep = DependencySet::Permanent(folded);
            let other_canonical = self.get_canonical_node(other_node);
            self.merge_nodes(other_canonical, new_root_node, &dep);
        }
        // `NominalIntroductionManager.applyNIRule`:171 — nominalIntorductionFinished.
        self.monitor_event(|m| m.nominal_introduction_finished());
        true
    }

    /// `NominalIntroductionBranchingPoint.startNextChoice`: try the target node
    /// against the next candidate NI root node.
    fn ni_start_next_choice(&mut self, level: i32, clash_dependency_set: &DependencySet) {
        let mut ni = self.branching_points[level as usize]
            .nominal_introduction
            .clone()
            .expect("NI branching point");
        ni.current_root_node += 1;
        let cardinality = ni.annotated_equality.cardinality();
        let mut dependency_set = self.dependency_set_factory.get_permanent(clash_dependency_set);
        if ni.current_root_node == cardinality {
            dependency_set = self
                .dependency_set_factory
                .remove_branching_point(&DependencySet::Permanent(dependency_set), level);
        }
        let dependency_set = DependencySet::Permanent(dependency_set);

        let new_root_node = self.ni_root_for(
            &dependency_set,
            ni.root_node,
            &ni.annotated_equality,
            ni.current_root_node,
        );
        let (new_root_node, dependency_set) =
            self.canonicalize_ni_root(new_root_node, &dependency_set);
        // Java `startNextChoice` line 220: `m_mergingManager.mergeNodes(m_niTargetNode,
        // newRootNode, dependencySet);` -- the RAW `m_niTargetNode` is passed, with no
        // canonicalization and no dependency-set fold. If `m_niTargetNode` has since
        // been merged away it is inactive, so `mergeNodes` returns false (a no-op);
        // otherwise it is still its own canonical node. Mirror Java exactly: pass the
        // raw node and do not fold its merge-chain dependency set.
        self.merge_nodes(ni.ni_target_node, new_root_node, &dependency_set);
        // Java `startNextChoice` lines 221-223:
        //   if (!m_otherNode.isPruned()) {
        //       dependencySet=m_otherNode.addCanonicalNodeDependencySet(dependencySet);
        //       m_mergingManager.mergeNodes(m_otherNode.getCanonicalNode(),newRootNode,dependencySet);
        //   }
        // The other node's merge-chain dependency set must be folded in BEFORE merging
        // its canonical survivor. Omitting this fold loses the branching
        // points `other_node`'s merge depended on, so a clash from this merge can
        // backtrack to the wrong branching point -> unsound result.
        if !self.nodes[ni.other_node].is_pruned() {
            let folded =
                self.add_canonical_node_dependency_set(ni.other_node, &dependency_set);
            let dependency_set = DependencySet::Permanent(folded);
            let other_canonical = self.get_canonical_node(ni.other_node);
            self.merge_nodes(other_canonical, new_root_node, &dependency_set);
        }
        self.branching_points[level as usize].nominal_introduction = Some(ni);
    }

    /// Port of `IndividualReuseStrategy.IndividualReuseBranchingPoint.
    /// startNextChoice`: a clash depended on a witness-reuse decision, so abandon
    /// the reuse and retry by creating a FRESH tree successor for the existential
    /// `>=1 r.C` instead.
    ///
    /// Java (`IndividualReuseStrategy.java:200-211`):
    /// ```java
    /// if (!m_wasParentReuse)
    ///     m_dontReuseConceptsThisRun.add((AtomicConcept)m_existential.getToConcept());
    /// DependencySet dependencySet=tableau.getDependencySetFactory()
    ///     .removeBranchingPoint(clashDependencySet,m_level);
    /// Node existentialNode=tableau.createNewTreeNode(dependencySet,m_node);
    /// m_extensionManager.addConceptAssertion(m_existential.getToConcept(),existentialNode,dependencySet,true);
    /// m_extensionManager.addRoleAssertion(m_existential.getOnRole(),m_node,existentialNode,dependencySet,true);
    /// ```
    /// Marking the to-concept "don't reuse this run" makes the next reuse attempt
    /// on that concept fall through to fresh creation, which (with the inexact
    /// strategy + the final-chance revalidation pass) keeps reuse sound+complete.
    fn reuse_start_next_choice(&mut self, level: i32, clash_dependency_set: &DependencySet) {
        let reuse = self.branching_points[level as usize]
            .reuse
            .clone()
            .expect("reuse branching point");
        let to_concept = reuse.existential.to_concept().clone();
        if !reuse.was_parent_reuse {
            if let crate::model::LiteralConcept::AtomicConcept(atomic) = &to_concept {
                if let Some(strategy) = self.individual_reuse_strategy.as_mut() {
                    strategy.add_dont_reuse_this_run(atomic.clone());
                }
            }
        }
        let permanent = self
            .dependency_set_factory
            .remove_branching_point(clash_dependency_set, level);
        let dependency_set = DependencySet::Permanent(permanent);
        self.monitor_event(|m| m.existential_expansion_started());
        let existential_node = self.create_new_tree_node(&dependency_set, reuse.for_node);
        self.add_concept_assertion(
            Concept::from(to_concept),
            existential_node,
            &dependency_set,
            true,
        );
        let on_role = reuse.existential.on_role().clone();
        self.add_role_assertion(
            on_role,
            reuse.for_node,
            existential_node,
            &dependency_set,
            true,
        );
        self.monitor_event(|m| m.existential_expansion_finished());
    }

    // -- Branching points ----------------------------------------------------

    fn current_level(&self) -> usize {
        self.current_branching_point as usize
    }

    /// Port of the `perTestNegativeFactsDummyDependency` setup in
    /// `Tableau.isSatisfiable`: push a base `BranchingPoint` and mark it the
    /// non-backtrackable level, then return the dependency set carrying that
    /// branching point. Per-test facts loaded with this dependency set never
    /// contribute to any *empty*-dependency derivation, so deterministic
    /// (empty-dependency) consequences read off the model afterwards are those of
    /// the empty-dependency facts alone -- the basis of
    /// `readKnownSubsumersFromRootNode` after the batched subsumption test.
    pub(crate) fn push_dummy_dependency_branching_point(
        &mut self,
    ) -> crate::tableau::dependency_set::PermanentDependencySet {
        let branching_point = BranchingPointData {
            level: 0,
            last_tableau_node: self.last_tableau_node,
            last_merged_or_pruned_node: self.last_merged_or_pruned_node,
            first_ground_disjunction: self.first_ground_disjunction,
            first_unprocessed_ground_disjunction: self.first_unprocessed_ground_disjunction,
            ground_disjunction: 0,
            sorted_disjunct_indexes: Vec::new(),
            current_index: 0,
            nominal_introduction: None,
            reuse: None,
        };
        self.push_branching_point(branching_point);
        // This branching point holds the per-test negations; backtracking must
        // never start a next choice on it (it is not a real disjunction).
        self.nonbacktrackable_branching_point = self.current_branching_point;
        let empty = DependencySet::Permanent(self.dependency_set_factory.empty_set());
        self.dependency_set_factory
            .add_branching_point(&empty, self.current_branching_point)
    }

    pub(crate) fn push_branching_point(&mut self, mut branching_point: BranchingPointData) {
        // `Tableau.pushBranchingPoint`:513 — pushBranchingPointStarted.
        self.monitor_event(|m| m.push_branching_point_started());
        self.current_branching_point += 1;
        branching_point.level = self.current_branching_point;
        self.branching_points.push(branching_point);
        let level = self.current_level();
        self.binary_extension_table.branching_point_pushed(level);
        self.ternary_extension_table.branching_point_pushed(level);
        self.description_graph_manager.branching_point_pushed(level);
        if level >= self.expanded_existentials_by_branching_point.len() {
            self.expanded_existentials_by_branching_point.resize(level + 1, 0);
        }
        self.expanded_existentials_by_branching_point[level] = self.expanded_existentials.len();
        // `NominalIntroductionManager.branchingPointPushed`: record the NI-root
        // table watermark for this level so `backtrack_to` can truncate it.
        if level >= self.ni_roots_by_branching_point.len() {
            self.ni_roots_by_branching_point.resize(level + 1, 0);
        }
        self.ni_roots_by_branching_point[level] = self.ni_roots_log.len();
        // `NominalIntroductionManager.branchingPointPushed`: record the buffered
        // annotated-equality watermarks (read cursor + buffer size) for this level
        // so `backtrack_to` can restore the cursor and truncate the buffer.
        if level >= self.annotated_equalities_by_branching_point.len() {
            self.annotated_equalities_by_branching_point.resize(level + 1, 0);
            self.first_unprocessed_ae_by_branching_point.resize(level + 1, 0);
        }
        self.first_unprocessed_ae_by_branching_point[level] =
            self.first_unprocessed_annotated_equality;
        self.annotated_equalities_by_branching_point[level] = self.annotated_equalities.len();
        // `IndividualReuseStrategy.branchingPointPushed`: record the reuse-table
        // watermark for this level so `backtrack` can drop reuse entries.
        if let Some(strategy) = self.individual_reuse_strategy.as_mut() {
            strategy.branching_point_pushed(level);
        }
        // `Tableau.pushBranchingPoint`:527 — pushBranchingPointFinished.
        self.monitor_event(|m| m.push_branching_point_finished());
    }

    fn backtrack_to(&mut self, new_current_branching_point: i32) {
        self.monitor_event(|m| m.backtrack_to_started()); // backtrackToStarted
        let branching_point =
            self.branching_points[new_current_branching_point as usize].clone();
        self.branching_points
            .truncate((new_current_branching_point + 1) as usize);
        self.current_branching_point = new_current_branching_point;

        // Ground disjunctions.
        self.first_unprocessed_ground_disjunction =
            branching_point.first_unprocessed_ground_disjunction;
        let should_be = branching_point.first_ground_disjunction;
        while self.first_ground_disjunction != should_be {
            let gd = self.first_ground_disjunction.unwrap();
            let next = self.ground_disjunctions[gd].as_ref().unwrap().next;
            self.destroy_ground_disjunction(gd);
            self.first_ground_disjunction = next;
        }
        if let Some(gd) = self.first_ground_disjunction {
            self.ground_disjunctions[gd].as_mut().unwrap().previous = None;
        }

        // Existentials. Java backtracks the expansion *strategy* first
        // (`m_existentialExpansionStrategy.backtrack()`, `Tableau.backtrackTo:553`)
        // and then the expansion *manager* (`m_existentialExpasionManager.backtrack()`,
        // `:554`).
        // `IndividualReuseStrategy.backtrack`: drop the reuse representatives
        // introduced after this branching point. The reused witness NODES
        // are destroyed below by `destroy_last_tableau_node`; clearing the reuse
        // map here keeps it from pointing at freed/reused node ids.
        if let Some(mut strategy) = self.individual_reuse_strategy.take() {
            strategy.backtrack(self.current_level());
            self.individual_reuse_strategy = Some(strategy);
        }
        self.backtrack_existentials();
        // NI-root dedup index (`NominalIntroductionManager.backtrack`): drop the
        // entries created after this branching point; the NI nodes themselves are
        // destroyed below by `destroy_last_tableau_node`, so leaving the keys would
        // leave them pointing at freed/reused node ids.
        self.backtrack_ni_roots();
        // Buffered annotated equalities (`NominalIntroductionManager.backtrack`):
        // restore the read cursor and truncate the buffer to this level's
        // watermark, releasing the dependency-set usages taken when buffering.
        self.backtrack_annotated_equalities();
        // Extension tables.
        self.backtrack_extension_tables();
        // Node merges/prunes.
        while self.last_merged_or_pruned_node != branching_point.last_merged_or_pruned_node {
            self.backtrack_last_merged_or_pruned_node();
        }
        // Created nodes.
        while self.last_tableau_node != branching_point.last_tableau_node {
            self.destroy_last_tableau_node();
        }
        self.clear_clash();
        self.monitor_event(|m| m.backtrack_to_finished()); // backtrackToFinished
    }

    fn backtrack_existentials(&mut self) {
        let level = self.current_level();
        let new_len = self.expanded_existentials_by_branching_point[level];
        while self.expanded_existentials.len() > new_len {
            let (existential, node) = self.expanded_existentials.pop().unwrap();
            self.nodes[node].unprocessed_existentials.push(existential);
        }
    }

    fn backtrack_ni_roots(&mut self) {
        let level = self.current_level();
        let new_len = self
            .ni_roots_by_branching_point
            .get(level)
            .copied()
            .unwrap_or(0);
        while self.ni_roots_log.len() > new_len {
            let key = self.ni_roots_log.pop().unwrap();
            self.ni_roots.remove(&key);
        }
    }

    fn backtrack_annotated_equalities(&mut self) {
        let level = self.current_level();
        // `NominalIntroductionManager.backtrack:82`: restore the read cursor.
        self.first_unprocessed_annotated_equality = self
            .first_unprocessed_ae_by_branching_point
            .get(level)
            .copied()
            .unwrap_or(0);
        // `:83-86`: truncate the buffer to the watermark, releasing usages.
        let new_len = self
            .annotated_equalities_by_branching_point
            .get(level)
            .copied()
            .unwrap_or(0);
        while self.annotated_equalities.len() > new_len {
            let buffered = self.annotated_equalities.pop().unwrap();
            self.dependency_set_factory
                .remove_usage(&buffered.dependency_set);
        }
    }

    fn backtrack_extension_tables(&mut self) {
        let level = self.current_level();
        let removed_binary = self
            .binary_extension_table
            .backtrack(level, &mut self.dependency_set_factory);
        for (tuple, is_core) in removed_binary {
            self.post_remove(&tuple, is_core);
        }
        let removed_ternary = self
            .ternary_extension_table
            .backtrack(level, &mut self.dependency_set_factory);
        for (tuple, is_core) in removed_ternary {
            self.post_remove(&tuple, is_core);
        }
        // The per-graph N-ary tables backtrack too; each removed tuple unlinks its
        // occurrence records (DescriptionGraphManager.descriptionGraphTupleRemoved).
        self.description_graph_manager
            .backtrack(level, &mut self.dependency_set_factory);
    }

    fn post_remove(&mut self, tuple: &[TableauObject], is_core: bool) {
        // AnywhereBlocking assertionRemoved: removing an atomic-concept assertion,
        // or (under pairwise blocking) a role edge, changes a node's blocking
        // signature.
        match &tuple[0] {
            TableauObject::Concept(Concept::AtomicConcept(_)) => {
                if let Some(node) = tuple[1].as_node() {
                    if self.blocking_validator.is_some() && !is_core {
                        // Validated blocking signs on the core concept label: a
                        // non-core atomic removal changes only the validation label
                        // (`ValidatedDirectBlockingChecker.removeConcept` sets
                        // `m_hasChangedForBlocking` / returns the node only when
                        // `isCore`). Invalidate the cached labels and mark the node
                        // (and parent) validation-changed without touching the
                        // blocking frontier or blocking-info-changed flag.
                        self.nodes[node].invalidate_blocking_cache();
                        self.nodes[node].has_blocking_info_changed = false;
                        self.validation_info_changed(node);
                        self.validation_info_changed_parent(node);
                    } else {
                        self.note_blocking_node_changed(node);
                        // AnywhereValidatedBlocking.assertionRemoved(Concept) also
                        // marks the node's parent validation info.
                        self.validation_info_changed_parent(node);
                    }
                }
            }
            TableauObject::DLPredicate(DLPredicate::AtomicRole(_)) => {
                let n1 = tuple[1].as_node();
                let n2 = tuple.get(2).and_then(|o| o.as_node());
                if self.blocking_validator.is_some() {
                    // AnywhereValidatedBlocking.assertionRemoved(AtomicRole):
                    //   updateNodeChange(directChecker.assertionRemoved(...)) -- which
                    //   returns null for a role, so a no-op -- then
                    //   validationInfoChanged(from); validationInfoChanged(to).
                    // No blocking-frontier move and no label-cache invalidation: only
                    // the validation frontier is rewound for both endpoints.
                    if let Some(n1) = n1 {
                        self.validation_info_changed(n1);
                    }
                    if let Some(n2) = n2 {
                        self.validation_info_changed(n2);
                    }
                } else if self.direct_blocking_kind
                    == crate::tableau::blocking_strategy::DirectBlockingKind::Pairwise
                {
                    // PairWiseDirectBlockingChecker.assertionRemoved: only a
                    // parent-child edge changes the child's pairwise signature.
                    match (n1, n2) {
                        (Some(from), Some(to)) if self.nodes[to].get_parent() == Some(from) => {
                            self.note_blocking_node_changed(to);
                        }
                        (Some(from), Some(to)) if self.nodes[from].get_parent() == Some(to) => {
                            self.note_blocking_node_changed(from);
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        match &tuple[0] {
            TableauObject::Concept(concept) => {
                let node = tuple[1].as_node().expect("binary tuple argument is a node");
                match concept {
                    Concept::AtomicConcept(_) => {
                        self.nodes[node].number_of_positive_atomic_concepts -= 1;
                    }
                    Concept::AtomicNegationConcept(_) => {
                        self.nodes[node].number_of_negated_atomic_concepts -= 1;
                    }
                    _ => {
                        // ExistentialConcept: remove from the node's unprocessed set.
                        if let Some(existential) =
                            crate::tableau::extension_manager::concept_to_existential(concept)
                        {
                            let unprocessed = &mut self.nodes[node].unprocessed_existentials;
                            if let Some(pos) = unprocessed.iter().position(|e| e == &existential) {
                                unprocessed.remove(pos);
                            }
                        }
                    }
                }
            }
            TableauObject::NegatedAtomicRole(_) => {
                let node = tuple[1].as_node().expect("ternary tuple argument is a node");
                self.nodes[node].number_of_negated_role_assertions -= 1;
            }
            _ => {}
        }
        // `ExtensionTable.postRemove` emits `tupleRemoved` (ExtensionTable.java:182).
        self.monitor_event(|m| m.tuple_removed());
    }

    // -- The main calculus loop helpers --------------------------------------

    /// Records that an existential has been expanded (for backtracking) and
    /// removes it from the node's unprocessed set.
    pub(crate) fn record_existential_processed(
        &mut self,
        node: NodeId,
        existential: &crate::model::ExistentialConcept,
    ) {
        self.expanded_existentials.push((existential.clone(), node));
        // `Node.removeFromUnprocessedExistentials` removes a SINGLE occurrence: the
        // last element via a fast path, otherwise the first equal element.
        let unprocessed = &mut self.nodes[node].unprocessed_existentials;
        if unprocessed.last() == Some(existential) {
            unprocessed.pop();
        } else if let Some(pos) = unprocessed.iter().position(|e| e == existential) {
            unprocessed.remove(pos);
        }
    }

    /// Processes the first unprocessed ground disjunction, branching if needed.
    /// Returns whether work was done.
    pub fn process_first_ground_disjunction(&mut self) -> bool {
        while let Some(gd_index) = self.first_unprocessed_ground_disjunction {
            // `Tableau.doIteration`:438 — processGroundDisjunctionStarted fires at
            // the top of each loop iteration, before the prune/satisfied check.
            self.monitor_event(|m| m.process_ground_disjunction_started());
            let previous = self.ground_disjunctions[gd_index].as_ref().unwrap().previous;
            self.first_unprocessed_ground_disjunction = previous;
            if self.ground_disjunction_is_pruned(gd_index)
                || self.ground_disjunction_satisfied(gd_index)
            {
                // `Tableau.doIteration`:460 — a pruned/satisfied disjunction fires
                // groundDisjunctionSatisfied (the `else` branch in Java).
                self.monitor_event(|m| m.ground_disjunction_satisfied());
                // `Tableau.processGroundDisjunctions` calls `checkInterrupt()` once
                // per skipped (pruned/satisfied) ground disjunction.
                self.note_interrupt();
                continue;
            }
            let header_index = self.ground_disjunctions[gd_index].as_ref().unwrap().header_index;
            let sorted = self
                .ground_disjunction_header_manager
                .header(header_index)
                .get_sorted_disjunct_indexes();
            let num_disjuncts = self
                .ground_disjunction_header_manager
                .header(header_index)
                .dl_predicates()
                .len();
            let mut dependency_set = DependencySet::Permanent(
                self.ground_disjunctions[gd_index].as_ref().unwrap().dependency_set.clone(),
            );
            if num_disjuncts > 1 {
                let branching_point = BranchingPointData {
                    level: 0,
                    last_tableau_node: self.last_tableau_node,
                    last_merged_or_pruned_node: self.last_merged_or_pruned_node,
                    first_ground_disjunction: self.first_ground_disjunction,
                    first_unprocessed_ground_disjunction: self
                        .first_unprocessed_ground_disjunction,
                    ground_disjunction: gd_index,
                    sorted_disjunct_indexes: sorted.clone(),
                    current_index: 0,
                    nominal_introduction: None,
                    reuse: None,
                };
                self.push_branching_point(branching_point);
                let level = self.current_branching_point;
                let permanent = self.dependency_set_factory.add_branching_point(&dependency_set, level);
                dependency_set = DependencySet::Permanent(permanent);
            }
            // `Tableau.doIteration`:450 — disjunctProcessingStarted around the
            // addDisjunctToTableau of the first (sorted) disjunct.
            self.monitor_event(|m| m.disjunct_processing_started());
            self.add_disjunct_to_tableau(gd_index, sorted[0], dependency_set);
            // `Tableau.doIteration`:453-454 — disjunctProcessingFinished then
            // processGroundDisjunctionFinished after the disjunct is added.
            self.monitor_event(|m| m.disjunct_processing_finished());
            self.monitor_event(|m| m.process_ground_disjunction_finished());
            return true;
        }
        false
    }

    /// Dependency-directed backtracking after a clash. Returns whether a branch
    /// remains to try (false means unsatisfiable).
    pub fn backtrack_on_clash(&mut self) -> bool {
        let clash_dependency_set = match &self.clash_dependency_set {
            Some(d) => DependencySet::Permanent(d.clone()),
            None => return false,
        };
        let new_current = clash_dependency_set.get_maximum_branching_point();
        if new_current <= self.nonbacktrackable_branching_point {
            return false;
        }
        self.backtrack_to(new_current);
        // `Tableau.doIteration`:473/476 — startNextBranchingPointStarted/Finished
        // wrap the current branching point's startNextChoice.
        self.monitor_event(|m| m.start_next_branching_point_started());
        self.start_next_choice(new_current, &clash_dependency_set);
        self.monitor_event(|m| m.start_next_branching_point_finished());
        self.dependency_set_factory.remove_unused_sets();
        true
    }

    fn start_next_choice(&mut self, level: i32, clash_dependency_set: &DependencySet) {
        if self.branching_points[level as usize].nominal_introduction.is_some() {
            self.ni_start_next_choice(level, clash_dependency_set);
            return;
        }
        if self.branching_points[level as usize].reuse.is_some() {
            self.reuse_start_next_choice(level, clash_dependency_set);
            return;
        }
        let (gd_index, header_index, sorted, num_disjuncts, mut current_index) = {
            let bp = &self.branching_points[level as usize];
            let gd = bp.ground_disjunction;
            let header_index = self.ground_disjunctions[gd].as_ref().unwrap().header_index;
            let num = self
                .ground_disjunction_header_manager
                .header(header_index)
                .dl_predicates()
                .len();
            (
                gd,
                header_index,
                bp.sorted_disjunct_indexes.clone(),
                num,
                bp.current_index,
            )
        };
        // Port of `DisjunctionBranchingPoint.startNextChoice` lines 38-40 --
        // gated by `m_useDisjunctionLearning` (default true), bump the
        // backtracking count of the just-exhausted disjunct
        // `m_sortedDisjunctIndexes[m_currentIndex]` *before* advancing
        // `m_currentIndex`. Answer-neutral: only re-sorts disjunct order.
        if self.use_disjunction_learning {
            self.ground_disjunction_header_manager
                .header_mut(header_index)
                .increase_number_of_backtrackings(sorted[current_index]);
        }
        current_index += 1;
        self.branching_points[level as usize].current_index = current_index;

        self.monitor_event(|m| m.disjunct_processing_started());

        let mut dependency_set = self.dependency_set_factory.get_permanent(clash_dependency_set);
        if current_index + 1 == num_disjuncts {
            dependency_set = self
                .dependency_set_factory
                .remove_branching_point(&DependencySet::Permanent(dependency_set), level);
        }
        let dependency_set = DependencySet::Permanent(dependency_set);

        // Assert the negations of the previously-tried disjuncts.
        for previous_index in 0..current_index {
            let previous_disjunct = sorted[previous_index];
            let (predicate, start, arguments) = {
                let gd = self.ground_disjunctions[gd_index].as_ref().unwrap();
                let header = self.ground_disjunction_header_manager.header(gd.header_index);
                (
                    header.dl_predicates()[previous_disjunct].clone(),
                    header.disjunct_start(previous_disjunct),
                    gd.arguments.clone(),
                )
            };
            match predicate {
                DLPredicate::Equality | DLPredicate::AnnotatedEquality(_) => {
                    self.add_ternary(
                        TableauObject::DLPredicate(DLPredicate::Inequality),
                        arguments[start],
                        arguments[start + 1],
                        &dependency_set,
                        false,
                    );
                }
                DLPredicate::AtomicConcept(a) => {
                    self.add_concept_assertion(
                        Concept::from(a.get_negation()),
                        arguments[start],
                        &dependency_set,
                        false,
                    );
                }
                _ => {}
            }
        }
        // `DisjunctionBranchingPoint.startNextChoice`:59 — disjunctProcessingFinished
        // around the addDisjunctToTableau of the next chosen disjunct.
        self.add_disjunct_to_tableau(gd_index, sorted[current_index], dependency_set);
        self.monitor_event(|m| m.disjunct_processing_finished());
    }
}

#[cfg(test)]
mod ni_tests {
    use crate::model::{AnnotatedEquality, AtomicRole, LiteralConcept, AtomicConcept, Role};
    use crate::tableau::dependency_set::DependencySet;
    use crate::tableau::tableau::Tableau;

    #[test]
    fn at_most_over_nominal_triggers_ni_branching() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());

        // node2: a root (named) node owning the at-most restriction.
        let node2 = tableau.create_new_named_node(&empty);
        // node0, node1: tree successors with a *different* parent, so node2 is
        // not their parent (canForgetAnnotation is false).
        let other_parent = tableau.create_new_named_node(&empty);
        let node0 = tableau.create_new_tree_node(&empty, other_parent);
        let node1 = tableau.create_new_tree_node(&empty, other_parent);

        let annotated_equality = AnnotatedEquality::create(
            2,
            Role::AtomicRole(AtomicRole::create("http://example.org/r")),
            LiteralConcept::AtomicConcept(AtomicConcept::create("http://example.org/C")),
        );

        let before = tableau.current_branching_point;
        let changed = tableau.apply_annotated_equality(&annotated_equality, node0, node1, node2, &empty);
        assert!(changed);
        // An NI branching point was pushed (cardinality 2 > 1).
        assert_eq!(tableau.current_branching_point, before + 1);
        assert!(tableau
            .branching_points
            .last()
            .unwrap()
            .nominal_introduction
            .is_some());
        // The NI target (node0) was merged into a fresh NI root node.
        assert!(tableau.node(node0).is_merged());
    }

    #[test]
    fn cardinality_gt_one_annotated_equality_is_deferred_not_applied_eagerly() {
        // Java `NominalIntroductionManager.addAnnotatedEquality` buffers a
        // cardinality-`> 1` annotated equality and applies the NI rule (pushing
        // the branching point) only later in `processAnnotatedEqualities`. The
        // entry point `add_annotated_equality` must therefore NOT push a branching
        // point; `process_annotated_equalities` must.
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());

        let node2 = tableau.create_new_named_node(&empty); // root
        let other_parent = tableau.create_new_named_node(&empty);
        let node0 = tableau.create_new_tree_node(&empty, other_parent);
        let node1 = tableau.create_new_tree_node(&empty, other_parent);

        let annotated_equality = AnnotatedEquality::create(
            2,
            Role::AtomicRole(AtomicRole::create("http://example.org/r")),
            LiteralConcept::AtomicConcept(AtomicConcept::create("http://example.org/C")),
        );

        let before = tableau.current_branching_point;
        // Entry point: must buffer, not branch.
        let buffered = tableau.add_annotated_equality(&annotated_equality, node0, node1, node2, &empty);
        assert!(buffered, "addAnnotatedEquality returns true when it buffers");
        assert_eq!(
            tableau.current_branching_point, before,
            "no branching point may be pushed eagerly for a cardinality>1 equality"
        );
        assert_eq!(tableau.annotated_equalities.len(), 1, "equality must be buffered");
        assert_eq!(tableau.first_unprocessed_annotated_equality, 0);
        assert!(!tableau.node(node0).is_merged(), "NI must not have fired yet");

        // Drain phase: now the NI rule fires and the branching point is pushed.
        let changed = tableau.process_annotated_equalities();
        assert!(changed);
        assert_eq!(tableau.current_branching_point, before + 1);
        assert!(tableau.branching_points.last().unwrap().nominal_introduction.is_some());
        assert_eq!(tableau.first_unprocessed_annotated_equality, 1, "cursor advanced");
        assert!(tableau.node(node0).is_merged(), "NI target merged after draining");
    }

    #[test]
    fn buffered_annotated_equality_is_truncated_on_backtrack() {
        // The buffer is backtracked state (Java `NominalIntroductionManager.
        // backtrack`). An equality buffered AFTER a branching point must be
        // dropped when backtracking to that branching point, while one buffered
        // (and the branching point's watermark) before it survives.
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let annotated_equality = AnnotatedEquality::create(
            2,
            Role::AtomicRole(AtomicRole::create("http://example.org/r")),
            LiteralConcept::AtomicConcept(AtomicConcept::create("http://example.org/C")),
        );

        // Equality A: buffer then drain -> the NI rule pushes a branching point.
        let node2 = tableau.create_new_named_node(&empty);
        let parent_a = tableau.create_new_named_node(&empty);
        let node0 = tableau.create_new_tree_node(&empty, parent_a);
        let node1 = tableau.create_new_tree_node(&empty, parent_a);
        let before = tableau.current_branching_point;
        tableau.add_annotated_equality(&annotated_equality, node0, node1, node2, &empty);
        tableau.process_annotated_equalities();
        let ni_level = tableau.current_branching_point;
        assert_eq!(ni_level, before + 1, "NI rule pushed a branching point");
        assert_eq!(tableau.annotated_equalities.len(), 1);

        // Equality B: buffered AFTER the NI branching point (not drained).
        let node5 = tableau.create_new_named_node(&empty);
        let parent_b = tableau.create_new_named_node(&empty);
        let node3 = tableau.create_new_tree_node(&empty, parent_b);
        let node4 = tableau.create_new_tree_node(&empty, parent_b);
        tableau.add_annotated_equality(&annotated_equality, node3, node4, node5, &empty);
        assert_eq!(tableau.annotated_equalities.len(), 2, "B is buffered");

        // Backtracking to the NI branching point drops B (buffered after it) but
        // keeps A (whose entry the level's watermark already covered).
        tableau.backtrack_to(ni_level);
        assert_eq!(
            tableau.annotated_equalities.len(),
            1,
            "the equality buffered after the branching point must be truncated"
        );
        assert_eq!(
            tableau.first_unprocessed_annotated_equality, 1,
            "the read cursor is restored to the branching point's watermark"
        );
    }

    #[test]
    fn ni_root_cache_is_truncated_on_backtrack() {
        // The NI-root dedup index must be part of the
        // backtracked state (Java `NominalIntroductionManager.backtrack`). After
        // backtracking past the NI branching point the cached key must be gone,
        // otherwise it would resolve to the destroyed/reused NI node id.
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());

        let node2 = tableau.create_new_named_node(&empty);
        let other_parent = tableau.create_new_named_node(&empty);
        let node0 = tableau.create_new_tree_node(&empty, other_parent);
        let node1 = tableau.create_new_tree_node(&empty, other_parent);

        let annotated_equality = AnnotatedEquality::create(
            2,
            Role::AtomicRole(AtomicRole::create("http://example.org/r")),
            LiteralConcept::AtomicConcept(AtomicConcept::create("http://example.org/C")),
        );

        let before = tableau.current_branching_point;
        tableau.apply_annotated_equality(&annotated_equality, node0, node1, node2, &empty);
        // A `cardinality > 1` NI rule pushed a branching point and cached a root.
        assert_eq!(tableau.current_branching_point, before + 1);
        assert_eq!(tableau.ni_roots.len(), 1);
        assert_eq!(tableau.ni_roots_log.len(), 1);

        // Backtrack to the NI branching point: its watermark was taken before the
        // NI root was created, so the cache must be emptied.
        tableau.backtrack_to(before + 1);
        assert!(
            tableau.ni_roots.is_empty(),
            "ni_roots must be truncated on backtrack, not left pointing at a freed node"
        );
        assert!(tableau.ni_roots_log.is_empty());
    }

    // Soundness: in the NI-rule backtracking-retry path
    // (`ni_start_next_choice`, the port of `NominalIntroductionBranchingPoint.
    // startNextChoice`), the merge of `other_node`'s canonical survivor into the new
    // NI root must FOLD IN `other_node`'s merge-chain dependency set first
    // (Java line 222: `dependencySet=m_otherNode.addCanonicalNodeDependencySet(
    // dependencySet);`). Omitting the fold loses the branching points that
    // `other_node`'s own merge depended on, so a later clash from this merge would
    // backtrack to the wrong branching point.
    //
    // Deterministic trigger: fire the cardinality-2 NI rule once (this pushes the NI
    // branching point at level L and merges `other_node` into NI root #1 with a
    // dependency set that carries L). Then drive the retry directly with an EMPTY
    // clash dependency set. The dependency set used for the retry's `other_node`
    // merge must still carry L (folded from `other_node`'s merge chain).
    #[test]
    fn ni_retry_folds_other_node_merge_chain_dependency_set() {
        use crate::tableau::dependency_set::DependencySetOps;

        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());

        let node2 = tableau.create_new_named_node(&empty);
        let other_parent = tableau.create_new_named_node(&empty);
        let node0 = tableau.create_new_tree_node(&empty, other_parent);
        let node1 = tableau.create_new_tree_node(&empty, other_parent);

        let annotated_equality = AnnotatedEquality::create(
            2,
            Role::AtomicRole(AtomicRole::create("http://example.org/r")),
            LiteralConcept::AtomicConcept(AtomicConcept::create("http://example.org/C")),
        );

        tableau.apply_annotated_equality(&annotated_equality, node0, node1, node2, &empty);
        // The NI rule pushed a branching point; capture its level L.
        let level = tableau.current_branching_point;
        let ni = tableau.branching_points[level as usize]
            .nominal_introduction
            .clone()
            .expect("NI branching point");
        let other_node = ni.other_node;

        // After the first NI application `other_node` is merged into NI root #1, and
        // its merge dependency set carries the branching point L.
        assert!(tableau.node(other_node).is_merged());
        let other_merge_dep = tableau
            .node(other_node)
            .get_merged_into_dependency_set()
            .expect("other_node merge has a dependency set")
            .clone();
        assert!(
            other_merge_dep.contains_branching_point(level),
            "precondition: other_node's merge must carry branching point L"
        );

        // `other_node`'s canonical survivor BEFORE the retry: this is NI root #1, an
        // active node. The retry will merge exactly this node into NI root #2, so its
        // freshly-recorded `merged_into_dependency_set` is precisely the dependency set
        // the retry used for the `other_node` merge -- the value the fold affects.
        let survivor_before = tableau.get_canonical_node(other_node);
        assert!(
            tableau.node(survivor_before).is_active(),
            "precondition: other_node's survivor (NI root #1) is active before the retry"
        );

        // Drive the retry with an EMPTY clash dependency set (no branching points).
        let empty_clash = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        tableau.ni_start_next_choice(level, &empty_clash);

        // The retry merged `survivor_before` (NI root #1) into NI root #2. With the
        // fix the dependency set recorded for THAT merge must include L (folded
        // from `other_node`'s merge chain), even though the clash set was empty.
        // Without the fold it would be empty.
        assert!(
            tableau.node(survivor_before).is_merged(),
            "retry must merge other_node's survivor (NI root #1) into NI root #2"
        );
        let retry_merge_dep = tableau
            .node(survivor_before)
            .get_merged_into_dependency_set()
            .expect("retry merge records a dependency set")
            .clone();
        assert!(
            retry_merge_dep.contains_branching_point(level),
            "BUG A-1: retry's other_node merge dropped the merge-chain branching point L; \
             dependency-directed backtracking would target the wrong branching point"
        );
    }
}

#[cfg(test)]
mod reuse_branching_tests {
    use super::{BranchingPointData, ReuseBranchingData};
    use crate::configuration::{Configuration, ExistentialStrategyType};
    use crate::model::{
        AtLeastConcept, AtomicConcept, AtomicRole, Concept, LiteralConcept, Role,
    };
    use crate::tableau::dependency_set::DependencySet;
    use crate::tableau::tableau::Tableau;

    /// Direct port-fidelity test for `IndividualReuseStrategy.
    /// IndividualReuseBranchingPoint.startNextChoice`: driving the reuse
    /// branching point's next choice must (1) mark the filler concept
    /// "don't reuse this run" (when it was a model-reuse, not a parent-reuse),
    /// and (2) create a FRESH tree successor with the role + filler assertions.
    #[test]
    fn reuse_branching_point_retries_with_fresh_witness() {
        let mut configuration = Configuration::default();
        configuration.existential_strategy_type = ExistentialStrategyType::IndividualReuse;
        let mut tableau = Tableau::with_configuration(&configuration);
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());

        let a = tableau.create_new_named_node(&empty);
        let at_least = AtLeastConcept::create(
            1,
            Role::AtomicRole(AtomicRole::create("http://example.org/r")),
            LiteralConcept::AtomicConcept(AtomicConcept::create("http://example.org/C")),
        );

        let nodes_before = tableau.debug_node_count();
        // Push a model-reuse (was_parent_reuse=false) branching point, as
        // `expand_with_model_reuse` does for the first C-witness.
        let bp = BranchingPointData {
            level: 0,
            last_tableau_node: tableau.last_tableau_node,
            last_merged_or_pruned_node: tableau.last_merged_or_pruned_node,
            first_ground_disjunction: tableau.first_ground_disjunction,
            first_unprocessed_ground_disjunction: tableau.first_unprocessed_ground_disjunction,
            ground_disjunction: usize::MAX,
            sorted_disjunct_indexes: Vec::new(),
            current_index: 0,
            nominal_introduction: None,
            reuse: Some(ReuseBranchingData {
                existential: at_least.clone(),
                for_node: a,
                was_parent_reuse: false,
            }),
        };
        tableau.push_branching_point(bp);
        let level = tableau.current_branching_point;

        // Drive the retry directly (as `backtrack_on_clash` -> `start_next_choice`
        // would on a clash that depended on this reuse decision).
        tableau.start_next_choice(level, &empty);

        // A fresh tree successor was created for `a` (one more node).
        assert_eq!(
            tableau.debug_node_count(),
            nodes_before + 1,
            "retry must create a fresh witness node"
        );
        // The fresh successor carries the role edge `r(a, w)` and the filler `C(w)`.
        let witness = tableau.last_tableau_node.expect("fresh witness exists");
        assert!(
            tableau.contains_role_assertion(at_least.on_role(), a, witness),
            "fresh witness must be an r-successor of a"
        );
        assert!(
            tableau.contains_concept_assertion(
                &Concept::from(at_least.to_concept().clone()),
                witness
            ),
            "fresh witness must carry the filler concept C"
        );
        // The witness is a TREE node (createNewTreeNode), not the reused root.
        assert_eq!(tableau.node(witness).get_parent(), Some(a));
        // And C is now marked "don't reuse this run" (model-reuse case).
        let strategy = tableau
            .individual_reuse_strategy
            .as_ref()
            .expect("reuse strategy installed");
        assert!(
            !strategy.should_reuse(&AtomicConcept::create("http://example.org/C")),
            "the clashing filler must be marked don't-reuse-this-run"
        );
    }
}
