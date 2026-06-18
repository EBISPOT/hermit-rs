// Port of org.semanticweb.HermiT.blocking.BlockingValidator: the satisfaction
// predicates that the validator's recursive clause matching evaluates against
// the live extension tables.
//
// These are the leaves of `satisfiesDLClauseForBlockedX` -- `YConstraint`'s
// explicit satisfaction and `ConsequenceAtom.isSatisfied` -- implemented here
// as `impl Tableau` queries over the binary/ternary extension tables.
#![allow(dead_code)]

use rustc_hash::FxHashMap as HashMap;

use crate::blocking::dl_clause_info::{ArgumentType, ConsequenceAtom, DLClauseInfo, YConstraint};
use crate::model::{AtomicConcept, AtLeastConcept, Concept, DLClause, DLPredicate, Role};
use crate::tableau::node::NodeId;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;
use crate::tableau::View;

/// The runtime binding of a `DLClauseInfo`'s variables to tableau nodes during
/// the validator's matching (HermiT's mutable `m_xNode`/`m_yNodes`/`m_zNodes`).
#[derive(Debug, Clone)]
pub struct ClauseBinding {
    pub x_node: NodeId,
    pub y_nodes: Vec<Option<NodeId>>,
    pub z_nodes: Vec<Option<NodeId>>,
}

impl Tableau {
    /// Port of `YConstraint.isSatisfiedExplicitly`: every `X→Y` and `Y→X` role
    /// and every concept on `Y` is asserted.
    pub(crate) fn y_constraint_satisfied_explicitly(
        &self,
        constraint: &YConstraint,
        node_x: NodeId,
        node_y: NodeId,
    ) -> bool {
        for role in &constraint.x2y_roles {
            if !self.contains_role_assertion(&Role::AtomicRole(role.clone()), node_x, node_y) {
                return false;
            }
        }
        for role in &constraint.y2x_roles {
            if !self.contains_role_assertion(&Role::AtomicRole(role.clone()), node_y, node_x) {
                return false;
            }
        }
        for concept in &constraint.y_concepts {
            if !self.contains_concept_assertion(&Concept::AtomicConcept(concept.clone()), node_y) {
                return false;
            }
        }
        true
    }

    /// Port of `YConstraint.isSatisfiedViaMirroringY`: like the explicit check,
    /// but a validly-blocked `Yi`'s concepts are looked up on its blocker.
    pub(crate) fn y_constraint_satisfied_via_mirroring_y(
        &self,
        constraint: &YConstraint,
        node_x: NodeId,
        node_y: NodeId,
    ) -> bool {
        for role in &constraint.x2y_roles {
            if !self.contains_role_assertion(&Role::AtomicRole(role.clone()), node_x, node_y) {
                return false;
            }
        }
        for role in &constraint.y2x_roles {
            if !self.contains_role_assertion(&Role::AtomicRole(role.clone()), node_y, node_x) {
                return false;
            }
        }
        let node_y_mirror = if self.nodes[node_y].is_blocked()
            && !self.nodes[node_y].block_violates_parent_constraints
        {
            self.nodes[node_y].get_blocker().unwrap_or(node_y)
        } else {
            node_y
        };
        for concept in &constraint.y_concepts {
            if !self
                .contains_concept_assertion(&Concept::AtomicConcept(concept.clone()), node_y_mirror)
            {
                return false;
            }
        }
        true
    }

    /// Port of `checkAtLeastForNonblocked`: validate an at-least on a non-blocked
    /// node, unblocking (flagging `block_violates_parent_constraints`) just
    /// enough blocked successors to reach the required count.
    pub(crate) fn check_at_least_for_nonblocked(
        &mut self,
        atleast: &AtLeastConcept,
        nonblocked: NodeId,
    ) {
        let required = atleast.number();
        let concept = Concept::from(atleast.to_concept().clone());
        let successors = self.at_least_role_successors(atleast.on_role(), nonblocked);
        let mut suitable = 0;
        let mut possibly_invalid: Vec<NodeId> = Vec::new();
        for successor in successors {
            if suitable >= required {
                break;
            }
            if self.nodes[successor].is_blocked()
                && !self.nodes[successor].block_violates_parent_constraints
            {
                let blocker = self.nodes[successor].get_blocker().unwrap();
                if self.contains_concept_assertion(&concept, blocker) {
                    suitable += 1;
                } else {
                    possibly_invalid.push(successor);
                }
            } else if self.contains_concept_assertion(&concept, successor) {
                suitable += 1;
            }
        }
        for blocked in possibly_invalid {
            if suitable >= required {
                break;
            }
            if self.contains_concept_assertion(&concept, blocked) {
                self.nodes[blocked].block_violates_parent_constraints = true;
                suitable += 1;
            }
        }
    }

    /// Port of `ConsequenceAtom.isSatisfied` (the three variants), evaluated
    /// against the current binding and the actual blocked node `blocked_x`.
    pub(crate) fn consequence_atom_satisfied(
        &self,
        atom: &ConsequenceAtom,
        binding: &ClauseBinding,
        blocked_x: NodeId,
    ) -> bool {
        match atom {
            ConsequenceAtom::Simple { predicate, argument_types, argument_indexes } => {
                let nodes: Vec<NodeId> = argument_types
                    .iter()
                    .zip(argument_indexes)
                    .map(|(arg_type, &index)| match arg_type {
                        ArgumentType::XVar => binding.x_node,
                        ArgumentType::YVar => {
                            binding.y_nodes[index].expect("Y node bound")
                        }
                        ArgumentType::ZVar => {
                            binding.z_nodes[index].expect("Z node bound")
                        }
                    })
                    .collect();
                if matches!(predicate, DLPredicate::AnnotatedEquality(_)) {
                    // (yi == yj)@x: satisfied iff the two Y nodes are identical.
                    return nodes[0] == nodes[1];
                }
                match nodes.len() {
                    1 => self.contains_assertion_unary(predicate, nodes[0]),
                    2 => self.contains_assertion_binary(predicate, nodes[0], nodes[1]),
                    _ => false,
                }
            }
            ConsequenceAtom::X2YOrY2X { role, y_argument_index, is_x2y } => {
                let node_y = binding.y_nodes[*y_argument_index].expect("Y node bound");
                // The "real X": when Y is the actual blocked node's parent, use
                // the blocked node itself, else the bound X (the blocker).
                let node_x_real = if Some(node_y) == self.nodes[blocked_x].get_parent() {
                    blocked_x
                } else {
                    binding.x_node
                };
                let role = Role::AtomicRole(role.clone());
                if *is_x2y {
                    self.contains_role_assertion(&role, node_x_real, node_y)
                } else {
                    self.contains_role_assertion(&role, node_y, node_x_real)
                }
            }
            ConsequenceAtom::MirroredY { concept, y_argument_index } => {
                let node_y = binding.y_nodes[*y_argument_index].expect("Y node bound");
                let node_y_mirror = if self.nodes[node_y].is_blocked() {
                    self.nodes[node_y].get_blocker().expect("blocked node has a blocker")
                } else {
                    node_y
                };
                self.contains_concept_assertion(
                    &Concept::AtomicConcept(concept.clone()),
                    node_y_mirror,
                )
            }
        }
    }
}

impl Tableau {
    /// The `r`-successors of `node` (following an atomic role forwards, or an
    /// inverse role backwards through the stored atomic role).
    fn at_least_role_successors(&self, role: &Role, node: NodeId) -> Vec<NodeId> {
        let (predicate, positions, buffer, read_column) = match role {
            Role::AtomicRole(r) => (
                DLPredicate::AtomicRole(r.clone()),
                [0, 1, -1],
                [None, Some(TableauObject::Node(node)), None],
                2usize,
            ),
            Role::InverseRole(r) => (
                DLPredicate::AtomicRole(r.get_inverse_of().clone()),
                [0, -1, 2],
                [None, None, Some(TableauObject::Node(node))],
                1usize,
            ),
        };
        let mut buffer = buffer;
        buffer[0] = Some(TableauObject::DLPredicate(predicate));
        let retrieval = self.create_ternary_retrieval(positions, buffer, View::Total);
        retrieval
            .tuple_indices
            .iter()
            .filter_map(|&idx| {
                self.ternary_extension_table.get_tuple_object(idx, read_column).as_node()
            })
            .collect()
    }

    /// Port of `BlockingValidator.isSatisfiedAtLeastForBlocked`: whether the
    /// blocker can satisfy `atleast` -- either reusing the blocked node's parent
    /// edge, or via enough distinct suitable successors of the blocker (other
    /// than the blocker's parent).
    pub(crate) fn is_satisfied_at_least_for_blocked(
        &self,
        atleast: &AtLeastConcept,
        blocked_x: NodeId,
        blocker: NodeId,
        blocker_parent: Option<NodeId>,
    ) -> bool {
        let role = atleast.on_role();
        let concept = Concept::from(atleast.to_concept().clone());
        if let Some(blocked_x_parent) = self.nodes[blocked_x].get_parent() {
            if self.contains_role_assertion(role, blocked_x, blocked_x_parent)
                && self.contains_concept_assertion(&concept, blocked_x_parent)
            {
                return true;
            }
        }
        let required = atleast.number();
        let mut suitable = 0;
        for successor in self.at_least_role_successors(role, blocker) {
            if suitable >= required {
                break;
            }
            if Some(successor) != blocker_parent
                && self.contains_concept_assertion(&concept, successor)
            {
                suitable += 1;
            }
        }
        suitable >= required
    }
}

/// Port of `org.semanticweb.HermiT.blocking.BlockingValidator` -- the
/// per-clause validity check that decides whether a (pairwise-)blocked node's
/// block is sound.
pub struct BlockingValidator {
    dl_clause_infos: Vec<DLClauseInfo>,
    by_x_concept: HashMap<AtomicConcept, Vec<usize>>,
    without_x_concept: Vec<usize>,
}

impl BlockingValidator {
    /// Builds the validator from the ontology's DL clauses, keeping only the
    /// GCIs that actually constrain successors (those with a `Yi` or `Zj`).
    pub fn new(dl_clauses: &indexmap::IndexSet<DLClause>) -> BlockingValidator {
        let mut dl_clause_infos: Vec<DLClauseInfo> = Vec::new();
        for clause in dl_clauses {
            if clause.is_general_concept_inclusion() {
                let info = DLClauseInfo::new(clause);
                if !info.y_variables.is_empty() || !info.z_variables.is_empty() {
                    dl_clause_infos.push(info);
                }
            }
        }
        let mut by_x_concept: HashMap<AtomicConcept, Vec<usize>> = HashMap::default();
        let mut without_x_concept: Vec<usize> = Vec::new();
        for (index, info) in dl_clause_infos.iter().enumerate() {
            if info.x_concepts.is_empty() {
                without_x_concept.push(index);
            } else {
                for x_concept in &info.x_concepts {
                    by_x_concept.entry(x_concept.clone()).or_default().push(index);
                }
            }
        }
        BlockingValidator { dl_clause_infos, by_x_concept, without_x_concept }
    }

    /// Port of `satisfiesConstraintsForBlockedX`: every clause whose `X` could
    /// match the blocker is satisfied around the blocked node.
    pub fn satisfies_constraints_for_blocked_x(&self, tableau: &Tableau, blocked_x: NodeId) -> bool {
        let blocker = match tableau.nodes[blocked_x].get_blocker() {
            Some(b) => b,
            None => return true,
        };
        let blocker_parent = tableau.nodes[blocker].get_parent();
        let retrieval = tableau.create_binary_retrieval(
            [-1, 1],
            [None, Some(TableauObject::Node(blocker))],
            View::Total,
        );
        for &idx in &retrieval.tuple_indices {
            match tableau.binary_extension_table.get_tuple_object(idx, 0) {
                TableauObject::Concept(Concept::AtomicConcept(c)) => {
                    if let Some(infos) = self.by_x_concept.get(c) {
                        for &info_index in infos {
                            if !self.satisfies_dl_clause_for_blocked_x(tableau, info_index, blocked_x) {
                                return false;
                            }
                        }
                    }
                }
                TableauObject::Concept(Concept::AtLeastConcept(atleast)) => {
                    if let Some(bp) = blocker_parent {
                        if tableau.contains_role_assertion(atleast.on_role(), blocker, bp)
                            && tableau.contains_concept_assertion(
                                &Concept::from(atleast.to_concept().clone()),
                                bp,
                            )
                            && !tableau.is_satisfied_at_least_for_blocked(
                                atleast, blocked_x, blocker, blocker_parent,
                            )
                        {
                            return false;
                        }
                    }
                }
                _ => {}
            }
        }
        for &info_index in &self.without_x_concept {
            if !self.satisfies_dl_clause_for_blocked_x(tableau, info_index, blocked_x) {
                return false;
            }
        }
        true
    }

    /// Port of `satisfiesDLClauseForBlockedX`: the clause holds around the
    /// blocked node, matching `X` to the blocker and one `Yi` to the blocked
    /// node's parent, for every Z/Y assignment.
    fn satisfies_dl_clause_for_blocked_x(
        &self,
        tableau: &Tableau,
        info_index: usize,
        blocked_x: NodeId,
    ) -> bool {
        let info = &self.dl_clause_infos[info_index];
        let blocked_x_parent = match tableau.nodes[blocked_x].get_parent() {
            Some(p) => p,
            None => return true,
        };
        let blocker = match tableau.nodes[blocked_x].get_blocker() {
            Some(b) => b,
            None => return true,
        };
        for c in &info.x_concepts {
            if !tableau.contains_concept_assertion(&Concept::AtomicConcept(c.clone()), blocker) {
                return true; // premise false -> trivially satisfied
            }
        }
        for r in &info.x2x_roles {
            if !tableau.contains_role_assertion(&Role::AtomicRole(r.clone()), blocker, blocker) {
                return true;
            }
        }
        // The clause is relevant only if some Y constraint links the blocked
        // node to its parent.
        let mut matching: Option<usize> = None;
        for (yi, yc) in info.y_constraints.iter().enumerate() {
            if tableau.y_constraint_satisfied_explicitly(yc, blocked_x, blocked_x_parent) {
                matching = Some(yi);
                break;
            }
        }
        let matching = match matching {
            Some(m) => m,
            None => return true,
        };
        let mut binding = ClauseBinding {
            x_node: blocker,
            y_nodes: vec![None; info.y_variables.len()],
            z_nodes: vec![None; info.z_variables.len()],
        };
        binding.y_nodes[matching] = Some(blocked_x_parent);
        self.match_blocked_z(tableau, info, blocked_x, matching, 0, &mut binding)
    }

    /// Recursive Z matching (`satisfiesDLClauseForBlockedXAndAnyZ`).
    fn match_blocked_z(
        &self,
        tableau: &Tableau,
        info: &DLClauseInfo,
        blocked_x: NodeId,
        matching: usize,
        to_match: usize,
        binding: &mut ClauseBinding,
    ) -> bool {
        if to_match == info.z_variables.len() {
            return self.match_blocked_y(tableau, info, blocked_x, matching, 0, binding);
        }
        let z_concepts = &info.z_concepts[to_match];
        let label = TableauObject::Concept(Concept::AtomicConcept(z_concepts[0].clone()));
        let retrieval = tableau.create_binary_retrieval([0, -1], [Some(label), None], View::Total);
        for &idx in &retrieval.tuple_indices {
            let node_z = match tableau.binary_extension_table.get_tuple_object(idx, 1).as_node() {
                Some(n) => n,
                None => continue,
            };
            let all_matched = z_concepts[1..].iter().all(|c| {
                tableau.contains_concept_assertion(&Concept::AtomicConcept(c.clone()), node_z)
            });
            if all_matched {
                binding.z_nodes[to_match] = Some(node_z);
                let result =
                    self.match_blocked_z(tableau, info, blocked_x, matching, to_match + 1, binding);
                binding.z_nodes[to_match] = None;
                if !result {
                    return false;
                }
            }
        }
        true
    }

    /// Recursive Y matching (`satisfiesDLClauseForBlockedXAnyZAndAnyY`).
    fn match_blocked_y(
        &self,
        tableau: &Tableau,
        info: &DLClauseInfo,
        blocked_x: NodeId,
        matching: usize,
        to_match: usize,
        binding: &mut ClauseBinding,
    ) -> bool {
        if to_match == matching {
            // The parent assignment is already fixed; skip it.
            return self.match_blocked_y(tableau, info, blocked_x, matching, to_match + 1, binding);
        }
        if to_match == info.y_constraints.len() {
            return self.satisfies_blocked_matched(tableau, info, blocked_x, binding);
        }
        let blocker = binding.x_node;
        let blocker_parent = tableau.nodes[blocker].get_parent();
        let yc = &info.y_constraints[to_match];
        for node_y in tableau.y_constraint_successors(yc, blocker) {
            if Some(node_y) != blocker_parent
                && tableau.y_constraint_satisfied_explicitly(yc, blocker, node_y)
            {
                binding.y_nodes[to_match] = Some(node_y);
                let result = self
                    .match_blocked_y(tableau, info, blocked_x, matching, to_match + 1, binding);
                binding.y_nodes[to_match] = None;
                if !result {
                    return false;
                }
            }
        }
        true
    }

    /// Port of `satisfiesDLClauseForBlockedXAndMatchedNodes`: at least one
    /// consequence must hold under the current binding.
    fn satisfies_blocked_matched(
        &self,
        tableau: &Tableau,
        info: &DLClauseInfo,
        blocked_x: NodeId,
        binding: &ClauseBinding,
    ) -> bool {
        info.consequences_for_blocked_x
            .iter()
            .any(|cons| tableau.consequence_atom_satisfied(cons, binding, blocked_x))
    }

    /// Port of `BlockingValidator.isBlockValid`: a candidate block is valid iff
    /// it does not violate the (now-validated) parent's constraints and the
    /// blocked node itself satisfies every applicable clause against its blocker.
    pub fn is_block_valid(&self, tableau: &mut Tableau, blocked: NodeId) -> bool {
        let blocked_parent = match tableau.nodes[blocked].get_parent() {
            Some(p) => p,
            None => return true,
        };
        if !tableau.nodes[blocked_parent].has_already_been_checked {
            self.reset_child_flags(tableau, blocked_parent);
            self.check_constraints_for_nonblocked_x(tableau, blocked_parent);
            tableau.nodes[blocked_parent].has_already_been_checked = true;
        }
        if tableau.nodes[blocked].block_violates_parent_constraints {
            return false;
        }
        self.satisfies_constraints_for_blocked_x(tableau, blocked)
    }

    /// Port of `resetChildFlags`: clear `block_violates_parent_constraints` on
    /// the parent's non-ancestor neighbours before re-checking it.
    fn reset_child_flags(&self, tableau: &mut Tableau, parent: NodeId) {
        let successors = tableau.create_ternary_retrieval(
            [-1, 1, -1],
            [None, Some(TableauObject::Node(parent)), None],
            View::Total,
        );
        let mut neighbours: Vec<NodeId> = successors
            .tuple_indices
            .iter()
            .filter_map(|&idx| tableau.ternary_extension_table.get_tuple_object(idx, 2).as_node())
            .collect();
        let predecessors = tableau.create_ternary_retrieval(
            [-1, -1, 2],
            [None, None, Some(TableauObject::Node(parent))],
            View::Total,
        );
        neighbours.extend(
            predecessors
                .tuple_indices
                .iter()
                .filter_map(|&idx| tableau.ternary_extension_table.get_tuple_object(idx, 1).as_node()),
        );
        for node in neighbours {
            if !tableau.is_ancestor_of(node, parent) {
                tableau.nodes[node].block_violates_parent_constraints = false;
            }
        }
    }

    // ---- Nonblocked-X side: check the blocked node's *parent*'s constraints,
    // flagging successor blocks that would violate them. ------------------------

    /// Port of `checkConstraintsForNonblockedX`: for the (non-blocked) parent of
    /// a candidate blocked node, validate its at-least and clause constraints,
    /// marking each successor whose block would invalidate them via
    /// `block_violates_parent_constraints`.
    pub fn check_constraints_for_nonblocked_x(&self, tableau: &mut Tableau, nonblocked_x: NodeId) {
        let retrieval = tableau.create_binary_retrieval(
            [-1, 1],
            [None, Some(TableauObject::Node(nonblocked_x))],
            View::Total,
        );
        let at_leasts: Vec<AtLeastConcept> = retrieval
            .tuple_indices
            .iter()
            .filter_map(|&idx| {
                match tableau.binary_extension_table.get_tuple_object(idx, 0) {
                    TableauObject::Concept(Concept::AtLeastConcept(a)) => Some(a.clone()),
                    _ => None,
                }
            })
            .collect();
        for atleast in at_leasts {
            tableau.check_at_least_for_nonblocked(&atleast, nonblocked_x);
        }
        for info_index in 0..self.dl_clause_infos.len() {
            self.check_dl_clause_for_nonblocked_x(tableau, info_index, nonblocked_x);
        }
    }

    /// Port of `checkDLClauseForNonblockedX`: if the premise matches the node,
    /// recursively match the Z and Y variables and flag invalid successor blocks.
    fn check_dl_clause_for_nonblocked_x(
        &self,
        tableau: &mut Tableau,
        info_index: usize,
        nonblocked_x: NodeId,
    ) {
        {
            let info = &self.dl_clause_infos[info_index];
            for c in &info.x_concepts {
                if !tableau.contains_concept_assertion(&Concept::AtomicConcept(c.clone()), nonblocked_x)
                {
                    return;
                }
            }
            for r in &info.x2x_roles {
                if !tableau.contains_role_assertion(
                    &Role::AtomicRole(r.clone()),
                    nonblocked_x,
                    nonblocked_x,
                ) {
                    return;
                }
            }
        }
        let (y_len, z_len) = {
            let info = &self.dl_clause_infos[info_index];
            (info.y_variables.len(), info.z_variables.len())
        };
        let mut binding = ClauseBinding {
            x_node: nonblocked_x,
            y_nodes: vec![None; y_len],
            z_nodes: vec![None; z_len],
        };
        self.check_nonblocked_z(tableau, info_index, nonblocked_x, 0, &mut binding);
    }

    /// Recursive Z matching for the nonblocked side
    /// (`checkDLClauseForNonblockedXAndAnyZ`). Z nodes are interchangeable in the
    /// model, so the first matching assignment suffices.
    fn check_nonblocked_z(
        &self,
        tableau: &mut Tableau,
        info_index: usize,
        nonblocked_x: NodeId,
        to_match: usize,
        binding: &mut ClauseBinding,
    ) {
        let z_len = self.dl_clause_infos[info_index].z_variables.len();
        if to_match == z_len {
            self.check_nonblocked_y(tableau, info_index, nonblocked_x, 0, binding);
            return;
        }
        let z_concepts = self.dl_clause_infos[info_index].z_concepts[to_match].clone();
        let label = TableauObject::Concept(Concept::AtomicConcept(z_concepts[0].clone()));
        let retrieval = tableau.create_binary_retrieval([0, -1], [Some(label), None], View::Total);
        let candidates: Vec<NodeId> = retrieval
            .tuple_indices
            .iter()
            .filter_map(|&idx| tableau.binary_extension_table.get_tuple_object(idx, 1).as_node())
            .collect();
        for node_z in candidates {
            let all_matched = z_concepts[1..].iter().all(|c| {
                tableau.contains_concept_assertion(&Concept::AtomicConcept(c.clone()), node_z)
            });
            if all_matched {
                binding.z_nodes[to_match] = Some(node_z);
                self.check_nonblocked_z(tableau, info_index, nonblocked_x, to_match + 1, binding);
                binding.z_nodes[to_match] = None;
                return; // any Z assignment works
            }
        }
    }

    /// Recursive Y matching for the nonblocked side
    /// (`checkDLClauseForNonblockedXAnyZAndAnyY`), using the mirroring
    /// satisfaction (a validly-blocked Y is matched via its blocker's label).
    fn check_nonblocked_y(
        &self,
        tableau: &mut Tableau,
        info_index: usize,
        nonblocked_x: NodeId,
        to_match: usize,
        binding: &mut ClauseBinding,
    ) {
        let y_len = self.dl_clause_infos[info_index].y_constraints.len();
        if to_match == y_len {
            self.check_nonblocked_matched(tableau, info_index, nonblocked_x, binding);
            return;
        }
        let yc = self.dl_clause_infos[info_index].y_constraints[to_match].clone();
        let candidates = tableau.y_constraint_successors(&yc, nonblocked_x);
        for node_y in candidates {
            if tableau.y_constraint_satisfied_via_mirroring_y(&yc, nonblocked_x, node_y) {
                binding.y_nodes[to_match] = Some(node_y);
                self.check_nonblocked_y(tableau, info_index, nonblocked_x, to_match + 1, binding);
                binding.y_nodes[to_match] = None;
            }
        }
    }

    /// Port of `checkDLClauseForNonblockedXAndMatchedNodes`: if any matched `Yi`
    /// is validly blocked and no consequence holds, break one such block by
    /// setting `block_violates_parent_constraints`.
    fn check_nonblocked_matched(
        &self,
        tableau: &mut Tableau,
        info_index: usize,
        nonblocked_x: NodeId,
        binding: &ClauseBinding,
    ) {
        let info = &self.dl_clause_infos[info_index];
        let contains_blocked_y = binding.y_nodes.iter().flatten().any(|&y| {
            tableau.nodes[y].is_blocked() && !tableau.nodes[y].block_violates_parent_constraints
        });
        if !contains_blocked_y {
            return;
        }
        // If some consequence already holds, nothing needs breaking.
        for cons in &info.consequences_for_nonblocked_x {
            if tableau.consequence_atom_satisfied(cons, binding, nonblocked_x) {
                return;
            }
        }
        // Break a block: a validly-blocked Yi missing a required concept that its
        // blocker carries.
        for i in (0..info.y_constraints.len()).rev() {
            let yi = match binding.y_nodes[i] {
                Some(y) => y,
                None => continue,
            };
            for c in &info.y_constraints[i].y_concepts {
                let concept = Concept::AtomicConcept(c.clone());
                if tableau.nodes[yi].is_blocked()
                    && !tableau.nodes[yi].block_violates_parent_constraints
                    && !tableau.contains_concept_assertion(&concept, yi)
                {
                    if let Some(blocker) = tableau.nodes[yi].get_blocker() {
                        if tableau.contains_concept_assertion(&concept, blocker) {
                            tableau.nodes[yi].block_violates_parent_constraints = true;
                            return;
                        }
                    }
                }
            }
        }
        // Otherwise break a block whose mirrored-Y consequence holds without
        // mirroring (the concept is on Yi itself).
        for cons in &info.consequences_for_nonblocked_x {
            if let ConsequenceAtom::MirroredY { concept, y_argument_index } = cons {
                if let Some(node_y) = binding.y_nodes[*y_argument_index] {
                    if tableau
                        .contains_concept_assertion(&Concept::AtomicConcept(concept.clone()), node_y)
                    {
                        tableau.nodes[node_y].block_violates_parent_constraints = true;
                        return;
                    }
                }
            }
        }
        // BlockingValidator.checkDLClauseForNonblockedXAndMatchedNodes ends with
        // `assert false`: reaching here means a block that should have been
        // breakable was not, which is an invariant violation.
        debug_assert!(false, "a block must always be breakable here");
    }
}

impl Tableau {
    /// The candidate `Yi` nodes for a constraint: the role successors of
    /// `node_x` along the constraint's `X→Y` role (or `Y→X` role backwards).
    fn y_constraint_successors(&self, constraint: &YConstraint, node_x: NodeId) -> Vec<NodeId> {
        if let Some(role) = constraint.x2y_roles.first() {
            self.at_least_role_successors(&Role::AtomicRole(role.clone()), node_x)
        } else if let Some(role) = constraint.y2x_roles.first() {
            // R(Y, node_x): the node_x is the "to" -- look backwards.
            self.at_least_role_successors(
                &Role::InverseRole(crate::model::InverseRole::create(role.clone())),
                node_x,
            )
        } else {
            Vec::new()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Atom, AtomicRole, LiteralConcept, Term, Variable};
    use crate::tableau::dependency_set::DependencySet;

    fn concept(name: &str) -> AtomicConcept {
        AtomicConcept::create(format!("http://example.org/{name}"))
    }
    fn role(name: &str) -> AtomicRole {
        AtomicRole::create(format!("http://example.org/{name}"))
    }

    #[test]
    fn y_constraint_and_consequence_satisfaction() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let x = tableau.create_new_named_node(&empty);
        let y = tableau.create_new_tree_node(&empty, x);

        // Assert R(x,y) and C(y).
        tableau.add_role_assertion(Role::AtomicRole(role("R")), x, y, &empty, true);
        tableau.add_concept_assertion(Concept::AtomicConcept(concept("C")), y, &empty, true);

        // YConstraint { x2y: R, y_concepts: C } is satisfied for (x, y).
        let yc = YConstraint {
            y_concepts: vec![concept("C")],
            x2y_roles: vec![role("R")],
            y2x_roles: vec![],
        };
        assert!(tableau.y_constraint_satisfied_explicitly(&yc, x, y));

        // A constraint requiring a missing y2x role is not satisfied.
        let yc_missing = YConstraint {
            y_concepts: vec![],
            x2y_roles: vec![],
            y2x_roles: vec![role("R")], // R(y,x) was not asserted
        };
        assert!(!tableau.y_constraint_satisfied_explicitly(&yc_missing, x, y));

        // A simple consequence C(Y0) is satisfied with Y0 bound to y.
        let binding = ClauseBinding { x_node: x, y_nodes: vec![Some(y)], z_nodes: vec![] };
        let cons_true = ConsequenceAtom::Simple {
            predicate: DLPredicate::AtomicConcept(concept("C")),
            argument_types: vec![ArgumentType::YVar],
            argument_indexes: vec![0],
        };
        assert!(tableau.consequence_atom_satisfied(&cons_true, &binding, y));

        // A simple consequence D(Y0) (not asserted) is not satisfied.
        let cons_false = ConsequenceAtom::Simple {
            predicate: DLPredicate::AtomicConcept(concept("D")),
            argument_types: vec![ArgumentType::YVar],
            argument_indexes: vec![0],
        };
        assert!(!tableau.consequence_atom_satisfied(&cons_false, &binding, y));

        // The role consequence R(X, Y0) holds (x2y direction).
        let cons_role = ConsequenceAtom::Simple {
            predicate: DLPredicate::AtomicRole(role("R")),
            argument_types: vec![ArgumentType::XVar, ArgumentType::YVar],
            argument_indexes: vec![0, 0],
        };
        assert!(tableau.consequence_atom_satisfied(&cons_role, &binding, y));
    }

    #[test]
    fn at_least_for_blocked_counts_suitable_successors() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        // A blocker with two distinct C-successors via role r, and an
        // (irrelevant) parent. A blocked node with a parent that does not help.
        let blocker_parent = tableau.create_new_named_node(&empty);
        let blocker = tableau.create_new_tree_node(&empty, blocker_parent);
        let s1 = tableau.create_new_tree_node(&empty, blocker);
        let s2 = tableau.create_new_tree_node(&empty, blocker);
        let blocked_x_parent = tableau.create_new_named_node(&empty);
        let blocked_x = tableau.create_new_tree_node(&empty, blocked_x_parent);

        let r = Role::AtomicRole(role("r"));
        tableau.add_role_assertion(r.clone(), blocker, s1, &empty, true);
        tableau.add_role_assertion(r.clone(), blocker, s2, &empty, true);
        tableau.add_concept_assertion(Concept::AtomicConcept(concept("C")), s1, &empty, true);
        tableau.add_concept_assertion(Concept::AtomicConcept(concept("C")), s2, &empty, true);

        let at_least_2 =
            AtLeastConcept::create(2, r.clone(), LiteralConcept::AtomicConcept(concept("C")));
        // The blocker has two suitable successors -> >= 2 r.C is satisfied.
        assert!(tableau.is_satisfied_at_least_for_blocked(
            &at_least_2,
            blocked_x,
            blocker,
            Some(blocker_parent)
        ));

        // >= 3 r.C is not satisfiable (only two suitable successors).
        let at_least_3 =
            AtLeastConcept::create(3, r.clone(), LiteralConcept::AtomicConcept(concept("C")));
        assert!(!tableau.is_satisfied_at_least_for_blocked(
            &at_least_3,
            blocked_x,
            blocker,
            Some(blocker_parent)
        ));

        // Ancestor relation: blocker_parent is an ancestor of s1.
        assert!(tableau.is_ancestor_of(blocker_parent, s1));
        assert!(!tableau.is_ancestor_of(s1, blocker_parent));
    }

    fn var(name: &str) -> Term {
        Term::Variable(Variable::create(name))
    }

    #[test]
    fn blocked_x_validation_checks_consequence() {
        // Clause: C(Y1) :- A(X), R(Y1, X)  -- a backward (Y->X) universal.
        let clause = DLClause::create(
            vec![Atom::create(DLPredicate::AtomicConcept(concept("C")), vec![var("Y1")])],
            vec![
                Atom::create(DLPredicate::AtomicConcept(concept("A")), vec![var("X")]),
                Atom::create(
                    DLPredicate::AtomicRole(role("R")),
                    vec![var("Y1"), var("X")],
                ),
            ],
        );
        let mut clauses = indexmap::IndexSet::new();
        clauses.insert(clause);
        let validator = BlockingValidator::new(&clauses);

        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let blocker = tableau.create_new_named_node(&empty);
        let parent = tableau.create_new_named_node(&empty);
        let blocked_x = tableau.create_new_tree_node(&empty, parent);

        // The blocker carries A; the blocked node has its parent's R-edge.
        tableau.add_concept_assertion(Concept::AtomicConcept(concept("A")), blocker, &empty, true);
        tableau.add_role_assertion(Role::AtomicRole(role("R")), parent, blocked_x, &empty, true);
        tableau.node_mut(blocked_x).set_blocked(Some(blocker), true);

        // Without C(parent), the clause's consequence fails -> block invalid.
        assert!(!validator.satisfies_constraints_for_blocked_x(&tableau, blocked_x));

        // Adding C(parent) makes the consequence hold -> block valid.
        tableau.add_concept_assertion(Concept::AtomicConcept(concept("C")), parent, &empty, true);
        assert!(validator.satisfies_constraints_for_blocked_x(&tableau, blocked_x));
    }

    #[test]
    fn nonblocked_x_flags_invalid_successor_block() {
        // Clause: C(Y1) :- A(X), R(X,Y1)  -- a forward universal A ⊑ ∀R.C.
        let clause = DLClause::create(
            vec![Atom::create(DLPredicate::AtomicConcept(concept("C")), vec![var("Y1")])],
            vec![
                Atom::create(DLPredicate::AtomicConcept(concept("A")), vec![var("X")]),
                Atom::create(DLPredicate::AtomicRole(role("R")), vec![var("X"), var("Y1")]),
            ],
        );
        let mut clauses = indexmap::IndexSet::new();
        clauses.insert(clause);
        let validator = BlockingValidator::new(&clauses);

        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        // nonblocked parent P with A and an R-successor Y that is blocked. The
        // forward universal has already derived C(Y) (the rule fired), but the
        // blocker -- which stands in for Y in the model -- lacks C, so the block
        // would violate ∀R.C and must be flagged invalid.
        let p = tableau.create_new_named_node(&empty);
        let y = tableau.create_new_tree_node(&empty, p);
        let blocker = tableau.create_new_named_node(&empty);

        tableau.add_concept_assertion(Concept::AtomicConcept(concept("A")), p, &empty, true);
        tableau.add_role_assertion(Role::AtomicRole(role("R")), p, y, &empty, true);
        tableau.add_concept_assertion(Concept::AtomicConcept(concept("C")), y, &empty, true);
        tableau.node_mut(y).set_blocked(Some(blocker), true);

        assert!(!tableau.node(y).block_violates_parent_constraints);
        validator.check_constraints_for_nonblocked_x(&mut tableau, p);
        // The blocker lacks C, so the block is invalid -> flagged.
        assert!(tableau.node(y).block_violates_parent_constraints);

        // If instead the blocker carries C, the block is valid -> no flag.
        let mut tableau2 = Tableau::new();
        let empty2 = DependencySet::Permanent(tableau2.dependency_set_factory().empty_set());
        let p2 = tableau2.create_new_named_node(&empty2);
        let y2 = tableau2.create_new_tree_node(&empty2, p2);
        let blocker2 = tableau2.create_new_named_node(&empty2);
        tableau2.add_concept_assertion(Concept::AtomicConcept(concept("A")), p2, &empty2, true);
        tableau2.add_role_assertion(Role::AtomicRole(role("R")), p2, y2, &empty2, true);
        tableau2.add_concept_assertion(Concept::AtomicConcept(concept("C")), y2, &empty2, true);
        tableau2.add_concept_assertion(Concept::AtomicConcept(concept("C")), blocker2, &empty2, true);
        tableau2.node_mut(y2).set_blocked(Some(blocker2), true);
        validator.check_constraints_for_nonblocked_x(&mut tableau2, p2);
        assert!(!tableau2.node(y2).block_violates_parent_constraints);
    }

    #[test]
    fn is_block_valid_composes_both_sides() {
        // Forward universal A ⊑ ∀R.C.
        let clause = DLClause::create(
            vec![Atom::create(DLPredicate::AtomicConcept(concept("C")), vec![var("Y1")])],
            vec![
                Atom::create(DLPredicate::AtomicConcept(concept("A")), vec![var("X")]),
                Atom::create(DLPredicate::AtomicRole(role("R")), vec![var("X"), var("Y1")]),
            ],
        );
        let mut clauses = indexmap::IndexSet::new();
        clauses.insert(clause);
        let validator = BlockingValidator::new(&clauses);

        // P:A, R(P,Y), C(Y), Y blocked by a blocker lacking C -> the block is
        // invalid (would violate the parent's ∀R.C).
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let p = tableau.create_new_named_node(&empty);
        let y = tableau.create_new_tree_node(&empty, p);
        let blocker = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(Concept::AtomicConcept(concept("A")), p, &empty, true);
        tableau.add_role_assertion(Role::AtomicRole(role("R")), p, y, &empty, true);
        tableau.add_concept_assertion(Concept::AtomicConcept(concept("C")), y, &empty, true);
        tableau.node_mut(y).set_blocked(Some(blocker), true);
        assert!(!validator.is_block_valid(&mut tableau, y));

        // With the blocker also carrying C, the block is valid.
        let mut tableau2 = Tableau::new();
        let empty2 = DependencySet::Permanent(tableau2.dependency_set_factory().empty_set());
        let p2 = tableau2.create_new_named_node(&empty2);
        let y2 = tableau2.create_new_tree_node(&empty2, p2);
        let blocker2 = tableau2.create_new_named_node(&empty2);
        tableau2.add_concept_assertion(Concept::AtomicConcept(concept("A")), p2, &empty2, true);
        tableau2.add_role_assertion(Role::AtomicRole(role("R")), p2, y2, &empty2, true);
        tableau2.add_concept_assertion(Concept::AtomicConcept(concept("C")), y2, &empty2, true);
        tableau2.add_concept_assertion(Concept::AtomicConcept(concept("C")), blocker2, &empty2, true);
        tableau2.node_mut(y2).set_blocked(Some(blocker2), true);
        assert!(validator.is_block_valid(&mut tableau2, y2));
    }
}
