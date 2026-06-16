// Port of org.semanticweb.HermiT.hierarchy.{AtomicConceptElement, InstanceManager}.
//
// `InstanceManager` answers `getInstances` / `getTypes` over the classified
// hierarchy using a "known / possible" instance cache per concept
// (`AtomicConceptElement`): an individual is a *known* instance of a concept, a
// *possible* one (not yet decided), or neither. The traversal pushes possibles
// up the hierarchy and only runs the (expensive) instance test when a possible
// has not already been confirmed, sharing results across the hierarchy.
//
// This port keeps that mechanism, parameterized by an `is_instance` oracle (the
// reasoner's instance test) so it is reusable and testable in isolation.

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

use crate::hierarchy::{Hierarchy, NodeRef};

/// Port of `AtomicConceptElement`: the known / possible instance sets of one
/// concept (individuals identified by their IRI).
#[derive(Debug, Default, Clone)]
pub struct AtomicConceptElement {
    known: HashSet<String>,
    possible: HashSet<String>,
}

impl AtomicConceptElement {
    pub fn is_known(&self, individual: &str) -> bool {
        self.known.contains(individual)
    }
    pub fn is_possible(&self, individual: &str) -> bool {
        self.possible.contains(individual)
    }
    pub fn has_possibles(&self) -> bool {
        !self.possible.is_empty()
    }
    pub fn known_instances(&self) -> &HashSet<String> {
        &self.known
    }
    /// `setToKnown`: promote a possible instance to a known one.
    pub fn set_to_known(&mut self, individual: &str) {
        self.possible.remove(individual);
        self.known.insert(individual.to_string());
    }
    /// `addPossible`.
    pub fn add_possible(&mut self, individual: &str) -> bool {
        self.possible.insert(individual.to_string())
    }
}

/// Port of `InstanceManager` (the class-instance side): caches the known /
/// possible instances of each hierarchy node's representative and answers
/// `getTypes`.
pub struct InstanceManager<E> {
    concept_to_element: HashMap<NodeRef, AtomicConceptElement>,
    _marker: std::marker::PhantomData<E>,
}

impl<E: Eq + Hash + Clone> Default for InstanceManager<E> {
    fn default() -> Self {
        InstanceManager { concept_to_element: HashMap::new(), _marker: std::marker::PhantomData }
    }
}

impl<E: Eq + Hash + Clone> InstanceManager<E> {
    pub fn new() -> InstanceManager<E> {
        InstanceManager::default()
    }

    /// Seed a possible instance of `node` (the read-off side of HermiT seeds
    /// `m_conceptToElement` before `getTypes` runs). The traversal only consults
    /// the oracle for nodes whose element marks the individual as possible
    /// (InstanceManager.java:945), so an unseeded node is never tested.
    pub fn add_possible(&mut self, node: NodeRef, individual: &str) {
        self.concept_to_element.entry(node).or_default().add_possible(individual);
    }

    /// `getTypes(individual, direct)`: the hierarchy nodes the individual is an
    /// instance of, using `is_instance` as the oracle (with the known/possible
    /// cache). `direct` returns only the most-specific such nodes.
    ///
    /// Port of `InstanceManager.getTypes`: traverse upward from the bottom node;
    /// when a node's concept is confirmed for the individual, record it and push
    /// the possibility to its parents.
    pub fn get_types<F>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        individual: &str,
        direct: bool,
        mut is_instance: F,
    ) -> HashSet<NodeRef>
    where
        F: FnMut(&E) -> bool,
    {
        let mut result: HashSet<NodeRef> = HashSet::new();
        let mut visited: HashSet<NodeRef> = HashSet::new();
        let mut to_process: VecDeque<NodeRef> = VecDeque::new();
        to_process.push_back(hierarchy.bottom_node());

        while let Some(current) = to_process.pop_front() {
            // Skip a node that is an ancestor of an already confirmed type.
            let descendants = hierarchy.descendant_nodes(current);
            let mut is_ancestor_of_result = false;
            for &r in &result {
                if descendants.contains(&r) {
                    is_ancestor_of_result = true;
                    break;
                }
            }
            if is_ancestor_of_result {
                visited.insert(current);
                continue;
            }

            let parents: Vec<NodeRef> = hierarchy.node(current).parent_nodes().iter().copied().collect();
            let representative = hierarchy.node(current).representative().clone();
            // Only run the (expensive) oracle when the node's element marks the
            // individual as a possible instance (InstanceManager.java:945).
            let is_possible = self
                .concept_to_element
                .get(&current)
                .map_or(false, |element| element.is_possible(individual));
            if is_possible {
                if is_instance(&representative) {
                    self.concept_to_element.entry(current).or_default().set_to_known(individual);
                } else {
                    // Push the individual as a possible to the parents.
                    for &parent in &parents {
                        self.concept_to_element.entry(parent).or_default().add_possible(individual);
                    }
                }
            }
            let is_known = self
                .concept_to_element
                .get(&current)
                .map_or(false, |element| element.is_known(individual));
            if is_known {
                if direct {
                    result.insert(current);
                } else {
                    for ancestor in hierarchy.ancestor_nodes(current) {
                        result.insert(ancestor);
                    }
                }
            } else {
                for parent in parents {
                    if !visited.contains(&parent) && !to_process.contains(&parent) {
                        to_process.push_back(parent);
                    }
                }
            }
            visited.insert(current);
        }
        result
    }
}

/// Port of `RoleElementManager.RoleElement`: the known / possible relation
/// pairs of one role, keyed by the source individual (individuals identified by
/// their IRI/string form). The role analog of `AtomicConceptElement`.
#[derive(Debug, Default, Clone)]
pub struct RoleElement {
    role: String,
    known_relations: HashMap<String, HashSet<String>>,
    possible_relations: HashMap<String, HashSet<String>>,
}

impl RoleElement {
    pub fn new(role: impl Into<String>) -> RoleElement {
        RoleElement {
            role: role.into(),
            known_relations: HashMap::new(),
            possible_relations: HashMap::new(),
        }
    }
    pub fn role(&self) -> &str {
        &self.role
    }
    pub fn is_known(&self, source: &str, target: &str) -> bool {
        self.known_relations.get(source).map_or(false, |s| s.contains(target))
    }
    pub fn is_possible(&self, source: &str, target: &str) -> bool {
        self.possible_relations.get(source).map_or(false, |s| s.contains(target))
    }
    pub fn known_relations(&self) -> &HashMap<String, HashSet<String>> {
        &self.known_relations
    }
    pub fn possible_relations(&self) -> &HashMap<String, HashSet<String>> {
        &self.possible_relations
    }
    pub fn has_possibles(&self) -> bool {
        !self.possible_relations.is_empty()
    }
    /// `setToKnown`: move a possible pair to the known set.
    pub fn set_to_known(&mut self, source: &str, target: &str) {
        if let Some(successors) = self.possible_relations.get_mut(source) {
            successors.remove(target);
            if successors.is_empty() {
                self.possible_relations.remove(source);
            }
        }
        self.add_known(source, target);
    }
    pub fn add_known(&mut self, source: &str, target: &str) -> bool {
        self.known_relations.entry(source.to_string()).or_default().insert(target.to_string())
    }
    pub fn remove_known(&mut self, source: &str, target: &str) -> bool {
        let removed = if let Some(successors) = self.known_relations.get_mut(source) {
            let r = successors.remove(target);
            if successors.is_empty() {
                self.known_relations.remove(source);
            }
            r
        } else {
            false
        };
        removed
    }
    pub fn add_possible(&mut self, source: &str, target: &str) -> bool {
        self.possible_relations.entry(source.to_string()).or_default().insert(target.to_string())
    }
    pub fn remove_possible(&mut self, source: &str, target: &str) -> bool {
        if let Some(successors) = self.possible_relations.get_mut(source) {
            let r = successors.remove(target);
            if successors.is_empty() {
                self.possible_relations.remove(source);
            }
            r
        } else {
            false
        }
    }
}

/// Port of `RoleElementManager`: the registry mapping each role to its
/// `RoleElement` (the role analog of the per-concept `AtomicConceptElement`
/// cache used by `InstanceManager`).
#[derive(Debug, Default)]
pub struct RoleElementManager {
    role_to_element: HashMap<String, RoleElement>,
}

impl RoleElementManager {
    pub fn new() -> RoleElementManager {
        RoleElementManager::default()
    }
    /// `getRoleElement`: the element for `role`, creating it on first use.
    pub fn get_role_element(&mut self, role: &str) -> &mut RoleElement {
        self.role_to_element.entry(role.to_string()).or_insert_with(|| RoleElement::new(role))
    }
}

// ===========================================================================
// Seeded class-instance manager (the read-off path).
//
// `SeededClassInstanceManager` is the concrete, hierarchy-keyed analogue of
// HermiT's `InstanceManager` class-instance side. Unlike the generic
// `InstanceManager<E>` above (a pure oracle traversal), this one is *seeded* by
// reading the saturated initial-consistency-check model:
//
//   * a deterministically-asserted atomic concept on an individual's node seeds
//     a KNOWN instance (`addKnownConceptInstance`);
//   * a non-deterministically-asserted one seeds a POSSIBLE instance
//     (`addPossibleConceptInstance`, `m_readingOffFoundPossibleConceptInstance`).
//
// `realize`/`get_types`/`get_instances` then read KNOWN instances directly and
// only run the (expensive) `is_instance` oracle for the POSSIBLE ones -- exactly
// HermiT's optimisation. Same-as equivalence classes are tracked alongside, from
// the model's individual merges (`initializeSameAs` / `computeSameAsEquivalenceClasses`).
// ===========================================================================

/// One read-off concept membership of an individual's node: the concept's IRI
/// and whether it was asserted deterministically (empty dependency set => known)
/// or not (=> possible). Mirrors the `m_binaryRetrieval1Bound` loop in
/// `InstanceManager.readOffTypes`.
#[derive(Debug, Clone)]
pub struct ReadOffConcept {
    /// The atomic concept's IRI.
    pub concept_iri: String,
    /// True iff the assertion's dependency set is empty (deterministic): a KNOWN
    /// membership. False => a POSSIBLE membership to be confirmed by the oracle.
    pub known: bool,
}

/// Port of `InstanceManager` (class-instance side), keyed by classified-hierarchy
/// node (`m_conceptToElement` is keyed by the representative concept; we key by
/// its `NodeRef`). The element is the per-node `AtomicConceptElement`.
pub struct SeededClassInstanceManager {
    /// `m_conceptToElement`: known/possible instances per hierarchy node.
    concept_to_element: HashMap<NodeRef, AtomicConceptElement>,
    /// Whether the read-off found any non-deterministic (possible) membership.
    /// `m_readingOffFoundPossibleConceptInstance`.
    reading_off_found_possible: bool,
    /// `m_individualToEquivalenceClass`: each individual to its (sorted) same-as
    /// set. The default BY_NAME policy keeps these flat.
    individual_to_equivalence_class: HashMap<String, Vec<String>>,
    /// `m_individualToPossibleEquivalenceClass` (flattened to individual pairs): a
    /// non-deterministic node merge in the initial model means the two individuals
    /// are *possibly* the same; `getSameAsIndividuals` confirms each via the oracle.
    /// Individuals never merged in the model are definitely distinct, so only these
    /// candidate pairs are ever tested.
    possible_equivalence_pairs: Vec<(String, String)>,
    /// `m_isInconsistent`.
    inconsistent: bool,
}

impl Default for SeededClassInstanceManager {
    fn default() -> Self {
        SeededClassInstanceManager {
            concept_to_element: HashMap::new(),
            reading_off_found_possible: false,
            individual_to_equivalence_class: HashMap::new(),
            possible_equivalence_pairs: Vec::new(),
            inconsistent: false,
        }
    }
}

impl SeededClassInstanceManager {
    pub fn new() -> SeededClassInstanceManager {
        SeededClassInstanceManager::default()
    }

    /// `setInconsistent`.
    pub fn set_inconsistent(&mut self) {
        self.inconsistent = true;
    }

    pub fn is_inconsistent(&self) -> bool {
        self.inconsistent
    }

    pub fn reading_off_found_possible(&self) -> bool {
        self.reading_off_found_possible
    }

    /// `initializeSameAs`: each named individual starts in its own singleton class;
    /// `same_as_pairs` are individual merges read off the model. A pair with an
    /// empty merge dependency set is a *deterministic* (definite) same-as, unioned
    /// immediately; a non-deterministic merge seeds the *possible* same-as set
    /// (`m_individualToPossibleEquivalenceClass`), confirmed lazily by the oracle in
    /// [`get_same_as_individuals`](Self::get_same_as_individuals).
    pub fn seed_same_as(&mut self, individuals: &[String], same_as_pairs: &[(String, String, bool)]) {
        for ind in individuals {
            self.individual_to_equivalence_class
                .entry(ind.clone())
                .or_insert_with(|| vec![ind.clone()]);
        }
        // Union-find over the deterministic merges first, so the possible links are
        // recorded against the final definite classes.
        for (a, b, definite) in same_as_pairs {
            if *definite {
                self.union_same_as(a, b);
            }
        }
        for (a, b, definite) in same_as_pairs {
            if !definite && !self.is_same_individual(a, b) {
                self.possible_equivalence_pairs.push((a.clone(), b.clone()));
            }
        }
    }

    fn union_same_as(&mut self, a: &str, b: &str) {
        let class_a = self
            .individual_to_equivalence_class
            .get(a)
            .cloned()
            .unwrap_or_else(|| vec![a.to_string()]);
        let class_b = self
            .individual_to_equivalence_class
            .get(b)
            .cloned()
            .unwrap_or_else(|| vec![b.to_string()]);
        if class_a == class_b {
            return;
        }
        let mut merged: Vec<String> = class_a;
        for x in class_b {
            if !merged.contains(&x) {
                merged.push(x);
            }
        }
        merged.sort();
        merged.dedup();
        for member in merged.clone() {
            self.individual_to_equivalence_class.insert(member, merged.clone());
        }
    }

    /// `getSameAsIndividuals(individual)`: the (sorted) same-as equivalence class.
    pub fn same_as_individuals(&self, individual: &str) -> Vec<String> {
        self.individual_to_equivalence_class
            .get(individual)
            .cloned()
            .unwrap_or_else(|| vec![individual.to_string()])
    }

    /// `isSameIndividual`.
    pub fn is_same_individual(&self, a: &str, b: &str) -> bool {
        a == b || self.same_as_individuals(a).contains(&b.to_string())
    }

    /// `getSameAsIndividuals(individual)`: the confirmed same-as equivalence class.
    /// Starting from the definite class, it expands over the *possible* equivalence
    /// pairs that touch the class, confirming each candidate with `is_same` (the
    /// `isSameIndividual` tableau oracle) and merging confirmed candidates (whose
    /// own possibles then extend the frontier). Refuted candidates are dropped so
    /// they are never retested. Only model-merged candidates are ever tested, never
    /// arbitrary pairs.
    pub fn get_same_as_individuals<F>(
        &mut self,
        individual: &str,
        mut is_same: F,
    ) -> Result<Vec<String>, String>
    where
        F: FnMut(&str, &str) -> Result<bool, String>,
    {
        use std::collections::HashSet;
        let mut class: HashSet<String> = self.same_as_individuals(individual).into_iter().collect();
        class.insert(individual.to_string());
        loop {
            // A candidate is a possible-equivalence pair with exactly one endpoint
            // already in the class.
            let candidate = self.possible_equivalence_pairs.iter().find_map(|(a, b)| {
                match (class.contains(a), class.contains(b)) {
                    (true, false) => Some(b.clone()),
                    (false, true) => Some(a.clone()),
                    _ => None,
                }
            });
            let Some(candidate) = candidate else { break };
            let anchor = class.iter().next().cloned().unwrap_or_else(|| individual.to_string());
            if is_same(&anchor, &candidate)? {
                // Confirmed: fold the candidate's whole definite class in (its own
                // possible pairs then extend the frontier on the next iteration).
                for member in self.same_as_individuals(&candidate) {
                    class.insert(member);
                }
                class.insert(candidate);
            } else {
                // Refuted: drop every possible pair linking the class to this
                // candidate so it is not retested.
                self.possible_equivalence_pairs
                    .retain(|(a, b)| !((class.contains(a) && *b == candidate)
                        || (class.contains(b) && *a == candidate)));
            }
        }
        // Record the confirmed class for every member (matches Java updating
        // m_individualToEquivalenceClass) and return it sorted.
        let mut members: Vec<String> = class.into_iter().collect();
        members.sort();
        members.dedup();
        for member in &members {
            self.individual_to_equivalence_class
                .insert(member.clone(), members.clone());
        }
        Ok(members)
    }

    /// Seed the known/possible class instances of one individual from its read-off
    /// node labels (`readOffTypes`). `node_for_element` maps a concept IRI to its
    /// classified-hierarchy node (skipping owl:Thing / internal / unknown). A label
    /// with `known=true` is a known instance; otherwise a possible instance.
    ///
    /// Java keeps each instance only at its MOST-SPECIFIC node(s)
    /// (`addKnownConceptInstance`, InstanceManager.java:724-741;
    /// `addPossibleConceptInstance`, 743-763). That invariant is restored as a
    /// hierarchy-aware batch pass in `normalize_concept_instances` (the port of the
    /// `setToClassifiedConceptHierarchy` cleanup, InstanceManager.java:270-294),
    /// which runs at the start of `realize`.
    pub fn read_off_types<F>(
        &mut self,
        individual: &str,
        labels: &[ReadOffConcept],
        mut node_for_element: F,
    ) where
        F: FnMut(&str) -> Option<NodeRef>,
    {
        for label in labels {
            if let Some(node) = node_for_element(&label.concept_iri) {
                let element = self.concept_to_element.entry(node).or_default();
                if label.known {
                    element.known.insert(individual.to_string());
                } else {
                    element.add_possible(individual);
                    self.reading_off_found_possible = true;
                }
            }
        }
    }

    /// Restore Java's most-specific-node invariant over the read-off cache:
    /// strip from every ancestor element the instances any descendant records.
    /// Port of the `setToClassifiedConceptHierarchy` cleanup
    /// (InstanceManager.java:270-294), which is the batch form of the per-insert
    /// `addKnownConceptInstance` / `addPossibleConceptInstance` invariants
    /// (724-763): traverse upward from the bottom node and, for each node's
    /// element, remove from every proper ancestor element the node's known
    /// instances (from the ancestor's known and possible sets) and the node's
    /// possible instances (from the ancestor's possible set).
    fn normalize_concept_instances<E>(&mut self, hierarchy: &Hierarchy<E>)
    where
        E: Eq + Hash + Clone,
    {
        let mut to_process: VecDeque<NodeRef> = VecDeque::new();
        let mut queued: HashSet<NodeRef> = HashSet::new();
        for &parent in hierarchy.node(hierarchy.bottom_node()).parent_nodes() {
            if queued.insert(parent) {
                to_process.push_back(parent);
            }
        }
        while let Some(current) = to_process.pop_front() {
            let current_known: HashSet<String>;
            let current_possible: HashSet<String>;
            match self.concept_to_element.get(&current) {
                Some(element) => {
                    current_known = element.known.clone();
                    current_possible = element.possible.clone();
                }
                None => continue,
            }
            let mut ancestors = hierarchy.ancestor_nodes(current);
            ancestors.remove(&current);
            for ancestor in ancestors {
                if let Some(ancestor_element) = self.concept_to_element.get_mut(&ancestor) {
                    for individual in &current_known {
                        ancestor_element.known.remove(individual);
                        ancestor_element.possible.remove(individual);
                    }
                    for individual in &current_possible {
                        ancestor_element.possible.remove(individual);
                    }
                }
            }
            for &parent in hierarchy.node(current).parent_nodes() {
                if queued.insert(parent) {
                    to_process.push_back(parent);
                }
            }
        }
    }

    /// `readOffClassInstancesByIndividual`'s tail: an individual with no read-off
    /// type becomes a KNOWN instance of `owl:Thing` (the top node). We call this
    /// for every relevant individual after the per-individual read-off so the top
    /// node's known set is the full relevant-individual set (matching Java, where
    /// `getInstancesForNode(top)` returns all relevant individuals and every
    /// individual's `getTypes` includes `owl:Thing`).
    pub fn seed_top_known(&mut self, top: NodeRef, individual: &str) {
        self.concept_to_element
            .entry(top)
            .or_default()
            .known
            .insert(individual.to_string());
    }

    /// `realize`: confirm every possible instance with the oracle, pushing the
    /// refuted ones up to the parents (so an ancestor node can still confirm them).
    /// After this, KNOWN instances of each node are exactly its instances.
    /// Mirrors `InstanceManager.realize`.
    pub fn realize<E, F>(&mut self, hierarchy: &Hierarchy<E>, mut is_instance: F)
    where
        E: Eq + Hash + Clone,
        F: FnMut(&E, &str) -> bool,
    {
        self.normalize_concept_instances(hierarchy);
        if !self.reading_off_found_possible {
            return;
        }
        let mut to_process: VecDeque<NodeRef> = VecDeque::new();
        let mut visited: HashSet<NodeRef> = HashSet::new();
        for &parent in hierarchy.node(hierarchy.bottom_node()).parent_nodes() {
            to_process.push_back(parent);
        }
        while let Some(current) = to_process.pop_front() {
            if !visited.insert(current) {
                continue;
            }
            let parents: Vec<NodeRef> =
                hierarchy.node(current).parent_nodes().iter().copied().collect();
            // Java guards the parent-enqueue (and the possible processing) with
            // `if (atomicConceptElement!=null)`: the upward traversal stops at
            // nodes that have no AtomicConceptElement.
            if self.concept_to_element.contains_key(&current) {
                for &parent in &parents {
                    if !visited.contains(&parent) && !to_process.contains(&parent) {
                        to_process.push_back(parent);
                    }
                }
            }
            let possibles: Vec<String> = match self.concept_to_element.get(&current) {
                Some(element) if element.has_possibles() => {
                    element.possible.iter().cloned().collect()
                }
                _ => continue,
            };
            let representative = hierarchy.node(current).representative().clone();
            let mut non_instances: Vec<String> = Vec::new();
            for individual in possibles {
                if is_instance(&representative, &individual) {
                    self.concept_to_element
                        .entry(current)
                        .or_default()
                        .known
                        .insert(individual);
                } else {
                    non_instances.push(individual);
                }
            }
            if let Some(element) = self.concept_to_element.get_mut(&current) {
                element.possible.clear();
            }
            let top = hierarchy.top_node();
            for &parent in &parents {
                // Java only promotes nonInstances to top's KNOWN set when top already
                // has an AtomicConceptElement; when the element is freshly created (for
                // top or any other parent) the nonInstances become POSSIBLE instances
                // (InstanceManager.java:849-860).
                let existed = self.concept_to_element.contains_key(&parent);
                let parent_element = self.concept_to_element.entry(parent).or_default();
                if parent == top && existed {
                    for ni in &non_instances {
                        parent_element.known.insert(ni.clone());
                    }
                } else {
                    for ni in &non_instances {
                        parent_element.add_possible(ni);
                    }
                }
            }
        }
        self.reading_off_found_possible = false;
    }

    /// `getInstances(node, direct)`: the named individuals that are instances of
    /// `node`'s concept. Assumes `realize` has run (so possibles are resolved into
    /// knowns). `child_is_type` decides, for the `direct` case, whether a known
    /// instance is also a known instance of some child node (then it is not direct).
    pub fn get_instances<E>(
        &self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        direct: bool,
        all_individuals: &HashSet<String>,
    ) -> HashSet<String>
    where
        E: Eq + Hash + Clone,
    {
        let mut result = HashSet::new();
        if node == hierarchy.bottom_node() {
            return result;
        }
        if !direct && node == hierarchy.top_node() {
            return all_individuals.clone();
        }
        self.collect_instances(hierarchy, node, direct, &mut result);
        result
    }

    fn collect_instances<E>(
        &self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        direct: bool,
        result: &mut HashSet<String>,
    ) where
        E: Eq + Hash + Clone,
    {
        if let Some(element) = self.concept_to_element.get(&node) {
            for individual in &element.known {
                let is_direct = if direct {
                    !hierarchy
                        .node(node)
                        .child_nodes()
                        .iter()
                        .any(|&child| self.is_known_of_descendant(hierarchy, child, individual))
                } else {
                    true
                };
                if is_direct {
                    result.insert(individual.clone());
                }
            }
        }
        if !direct {
            for &child in hierarchy.node(node).child_nodes() {
                if child != hierarchy.bottom_node() {
                    self.collect_instances(hierarchy, child, direct, result);
                }
            }
        }
    }

    fn is_known_of_descendant<E>(
        &self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        individual: &str,
    ) -> bool
    where
        E: Eq + Hash + Clone,
    {
        if node == hierarchy.bottom_node() {
            return false;
        }
        if self
            .concept_to_element
            .get(&node)
            .map_or(false, |e| e.is_known(individual))
        {
            return true;
        }
        hierarchy
            .node(node)
            .child_nodes()
            .iter()
            .any(|&child| self.is_known_of_descendant(hierarchy, child, individual))
    }

    /// `getTypes(individual, direct)`: the hierarchy nodes the individual is a
    /// (direct) instance of, reading KNOWN memberships directly. Assumes `realize`
    /// has resolved the possibles. Mirrors the post-realization `InstanceManager.getTypes`.
    pub fn get_types_of<E>(
        &self,
        hierarchy: &Hierarchy<E>,
        individual: &str,
        direct: bool,
    ) -> HashSet<NodeRef>
    where
        E: Eq + Hash + Clone,
    {
        let mut type_nodes: HashSet<NodeRef> = HashSet::new();
        for (&node, element) in &self.concept_to_element {
            if element.is_known(individual) {
                type_nodes.insert(node);
            }
        }
        if direct {
            let mut result = HashSet::new();
            for &node in &type_nodes {
                let has_more_specific = hierarchy
                    .node(node)
                    .child_nodes()
                    .iter()
                    .any(|child| type_nodes.contains(child));
                if !has_more_specific {
                    result.insert(node);
                }
            }
            result
        } else {
            // `getTypes(individual,false)`: `result.addAll(current.getAncestorNodes())`
            // for every node where the individual is known, so the result is closed
            // under ancestors (InstanceManager.java:961).
            let mut result: HashSet<NodeRef> = HashSet::new();
            for &node in &type_nodes {
                for ancestor in hierarchy.ancestor_nodes(node) {
                    result.insert(ancestor);
                }
            }
            result
        }
    }
}

// ===========================================================================
// Seeded object-role instance manager (the role read-off path).
//
// `SeededRoleInstanceManager` is the role analogue of
// `SeededClassInstanceManager`: it caches per-role known/possible relation pairs
// (`RoleElement`, keyed by classified role-hierarchy node) seeded from the
// saturated model, then `realize_object_roles` confirms the possibles with the
// `is_role_instance` oracle (pushing refuted pairs to parents), and the
// `get_object_property_*` traversals answer the role-instance queries. Port of
// `InstanceManager.realizeObjectRoles` (870-915) and `getObjectProperty*`
// (1080-1223).
// ===========================================================================

/// Port of `InstanceManager` (object-role side): the per-role-hierarchy-node
/// known/possible relation cache. `node_to_element[node]` is the `RoleElement`
/// of the node's representative role (Java's `m_currentRoleHierarchy` carries the
/// `RoleElement` as the node payload directly).
pub struct SeededRoleInstanceManager {
    /// The `RoleElement` of each role-hierarchy node's representative role.
    node_to_element: HashMap<NodeRef, RoleElement>,
    /// Whether the read-off found any non-deterministic (possible) relation.
    /// `m_readingOffFoundPossiblePropertyInstance`.
    reading_off_found_possible: bool,
    /// `m_isInconsistent`.
    inconsistent: bool,
}

impl Default for SeededRoleInstanceManager {
    fn default() -> Self {
        SeededRoleInstanceManager {
            node_to_element: HashMap::new(),
            reading_off_found_possible: false,
            inconsistent: false,
        }
    }
}

impl SeededRoleInstanceManager {
    pub fn new() -> SeededRoleInstanceManager {
        SeededRoleInstanceManager::default()
    }

    pub fn set_inconsistent(&mut self) {
        self.inconsistent = true;
    }

    pub fn is_inconsistent(&self) -> bool {
        self.inconsistent
    }

    pub fn reading_off_found_possible(&self) -> bool {
        self.reading_off_found_possible
    }

    fn element_mut(&mut self, node: NodeRef) -> &mut RoleElement {
        self.node_to_element.entry(node).or_insert_with(|| RoleElement::new(String::new()))
    }

    /// `addKnownRoleInstance` (InstanceManager.java:764-783): record the pair at
    /// its most-specific node -- skip if a descendant already records it as known,
    /// then strip it from every proper ancestor's known set.
    pub fn add_known_role_instance<E>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        source: &str,
        target: &str,
    ) where
        E: Eq + Hash + Clone,
    {
        if node == hierarchy.top_node() {
            return;
        }
        for descendant in hierarchy.descendant_nodes(node) {
            if descendant == node {
                continue;
            }
            if self
                .node_to_element
                .get(&descendant)
                .map_or(false, |e| e.is_known(source, target))
            {
                return;
            }
        }
        self.element_mut(node).add_known(source, target);
        let mut ancestors = hierarchy.ancestor_nodes(node);
        ancestors.remove(&node);
        for ancestor in ancestors {
            if let Some(element) = self.node_to_element.get_mut(&ancestor) {
                element.remove_known(source, target);
            }
        }
    }

    /// `addPossibleRoleInstance` (InstanceManager.java:784-806): record the pair as
    /// possible at its most-specific node -- skip if a descendant already records it
    /// as possible, then strip it from every proper ancestor's possible set.
    pub fn add_possible_role_instance<E>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        source: &str,
        target: &str,
    ) where
        E: Eq + Hash + Clone,
    {
        if node == hierarchy.top_node() {
            return;
        }
        for descendant in hierarchy.descendant_nodes(node) {
            if descendant == node {
                continue;
            }
            if self
                .node_to_element
                .get(&descendant)
                .map_or(false, |e| e.is_possible(source, target))
            {
                return;
            }
        }
        self.element_mut(node).add_possible(source, target);
        self.reading_off_found_possible = true;
        let mut ancestors = hierarchy.ancestor_nodes(node);
        ancestors.remove(&node);
        for ancestor in ancestors {
            if let Some(element) = self.node_to_element.get_mut(&ancestor) {
                element.remove_possible(source, target);
            }
        }
    }

    /// `realizeObjectRoles` (InstanceManager.java:870-915): traverse upward from
    /// the bottom node; confirm each node's possible relations with the oracle,
    /// promoting confirmed pairs to known and pushing refuted ones to the parents'
    /// possibles.
    ///
    /// Faithful to Java's quirk at line 898: the *subject* (`individual`), not the
    /// refuted `successor`, is collected into `nonInstances`, and that set is then
    /// pushed to each parent as possible successors of `individual`
    /// (`parentRepresentative.addPossibles(individual, nonInstances)`, 904).
    pub fn realize_object_roles<E, F>(&mut self, hierarchy: &Hierarchy<E>, mut is_role_instance: F)
    where
        E: Eq + Hash + Clone,
        F: FnMut(&E, &str, &str) -> bool,
    {
        if !self.reading_off_found_possible {
            return;
        }
        let top = hierarchy.top_node();
        let mut to_process: VecDeque<NodeRef> = VecDeque::new();
        let mut visited: HashSet<NodeRef> = HashSet::new();
        to_process.push_back(hierarchy.bottom_node());
        while let Some(current) = to_process.pop_front() {
            if !visited.insert(current) {
                continue;
            }
            let parents: Vec<NodeRef> =
                hierarchy.node(current).parent_nodes().iter().copied().collect();
            for &parent in &parents {
                if !visited.contains(&parent) && !to_process.contains(&parent) {
                    to_process.push_back(parent);
                }
            }
            let has_possibles = self
                .node_to_element
                .get(&current)
                .map_or(false, |e| e.has_possibles());
            if !has_possibles {
                continue;
            }
            let role = hierarchy.node(current).representative().clone();
            let subjects: Vec<String> = self
                .node_to_element
                .get(&current)
                .map(|e| e.possible_relations().keys().cloned().collect())
                .unwrap_or_default();
            for individual in subjects {
                let successors: Vec<String> = self
                    .node_to_element
                    .get(&current)
                    .and_then(|e| e.possible_relations().get(&individual))
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default();
                // Java collects the (buggy) subject for every refuted successor.
                let mut non_instances: HashSet<String> = HashSet::new();
                for successor in successors {
                    if is_role_instance(&role, &individual, &successor) {
                        self.element_mut(current).add_known(&individual, &successor);
                    } else {
                        non_instances.insert(individual.clone());
                    }
                }
                for &parent in &parents {
                    if parent == top {
                        continue;
                    }
                    let parent_element = self.element_mut(parent);
                    for ni in &non_instances {
                        parent_element.add_possible(&individual, ni);
                    }
                }
            }
            if let Some(element) = self.node_to_element.get_mut(&current) {
                element.possible_relations.clear();
            }
        }
        self.reading_off_found_possible = false;
    }

    /// `hasObjectRoleRelationship(node, individual1, individual2)`
    /// (InstanceManager.java:1087-1107).
    pub fn has_object_role_relationship<E, F>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        individual1: &str,
        individual2: &str,
        all_individuals: &HashSet<String>,
        is_role_instance: &mut F,
    ) -> bool
    where
        E: Eq + Hash + Clone,
        F: FnMut(&E, &str, &str) -> bool,
    {
        let is_top = node == hierarchy.top_node();
        if is_top
            || self
                .node_to_element
                .get(&node)
                .map_or(false, |e| e.is_known(individual1, individual2))
        {
            return true;
        }
        let contains_unknown =
            !all_individuals.contains(individual1) || !all_individuals.contains(individual2);
        let is_possible = self
            .node_to_element
            .get(&node)
            .map_or(false, |e| e.is_possible(individual1, individual2));
        if is_possible || contains_unknown {
            let role = hierarchy.node(node).representative().clone();
            if is_role_instance(&role, individual1, individual2) {
                if !contains_unknown {
                    self.element_mut(node).set_to_known(individual1, individual2);
                }
                return true;
            } else {
                let parents: Vec<NodeRef> =
                    hierarchy.node(node).parent_nodes().iter().copied().collect();
                for parent in parents {
                    self.element_mut(parent).add_possible(individual1, individual2);
                }
            }
        } else {
            let children: Vec<NodeRef> =
                hierarchy.node(node).child_nodes().iter().copied().collect();
            for child in children {
                if self.has_object_role_relationship(
                    hierarchy,
                    child,
                    individual1,
                    individual2,
                    all_individuals,
                    is_role_instance,
                ) {
                    return true;
                }
            }
        }
        false
    }

    /// `getObjectPropertyInstances(node)` (InstanceManager.java:1109-1158): all
    /// (subject, successor-set) pairs of the role, resolving possibles with the
    /// oracle and pushing refuted ones to parents.
    pub fn get_object_property_instances<E, F>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        all_individuals: &HashSet<String>,
        is_role_instance: &mut F,
    ) -> HashMap<String, HashSet<String>>
    where
        E: Eq + Hash + Clone,
        F: FnMut(&E, &str, &str) -> bool,
    {
        let mut result: HashMap<String, HashSet<String>> = HashMap::new();
        self.collect_object_property_instances(
            hierarchy,
            node,
            all_individuals,
            is_role_instance,
            &mut result,
        );
        result
    }

    fn collect_object_property_instances<E, F>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        all_individuals: &HashSet<String>,
        is_role_instance: &mut F,
        result: &mut HashMap<String, HashSet<String>>,
    ) where
        E: Eq + Hash + Clone,
        F: FnMut(&E, &str, &str) -> bool,
    {
        if node == hierarchy.top_node() || self.inconsistent {
            // Java shares one growing set across every subject; we materialise the
            // full relevant-individual cross product per subject (same membership).
            for individual in all_individuals {
                result.insert(individual.clone(), all_individuals.clone());
            }
            return;
        }
        let role = hierarchy.node(node).representative().clone();
        // Resolve the possibles.
        let possible_pairs: Vec<(String, String)> = self
            .node_to_element
            .get(&node)
            .map(|e| {
                e.possible_relations()
                    .iter()
                    .flat_map(|(s, ts)| ts.iter().map(move |t| (s.clone(), t.clone())))
                    .collect()
            })
            .unwrap_or_default();
        let parents: Vec<NodeRef> = hierarchy.node(node).parent_nodes().iter().copied().collect();
        for (subject, successor) in possible_pairs {
            if is_role_instance(&role, &subject, &successor) {
                self.element_mut(node).set_to_known(&subject, &successor);
            } else {
                for &parent in &parents {
                    self.element_mut(parent).add_possible(&subject, &successor);
                }
            }
        }
        // Collect the knowns.
        if let Some(element) = self.node_to_element.get(&node) {
            for (subject, successors) in element.known_relations() {
                if !all_individuals.contains(subject) {
                    continue;
                }
                let entry = result.entry(subject.clone()).or_default();
                for successor in successors {
                    if all_individuals.contains(successor) {
                        entry.insert(successor.clone());
                    }
                }
                if entry.is_empty() {
                    result.remove(subject);
                }
            }
        }
        let children: Vec<NodeRef> = hierarchy.node(node).child_nodes().iter().copied().collect();
        for child in children {
            self.collect_object_property_instances(
                hierarchy,
                child,
                all_individuals,
                is_role_instance,
                result,
            );
        }
    }

    /// `getObjectPropertyValues(node, subject)` (InstanceManager.java:1197-1223):
    /// the successors of `subject` under the role.
    pub fn get_object_property_values<E, F>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        subject: &str,
        all_individuals: &HashSet<String>,
        is_role_instance: &mut F,
    ) -> HashSet<String>
    where
        E: Eq + Hash + Clone,
        F: FnMut(&E, &str, &str) -> bool,
    {
        let mut result = HashSet::new();
        self.collect_object_property_values(
            hierarchy,
            node,
            subject,
            all_individuals,
            is_role_instance,
            &mut result,
        );
        result
    }

    fn collect_object_property_values<E, F>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        subject: &str,
        all_individuals: &HashSet<String>,
        is_role_instance: &mut F,
        result: &mut HashSet<String>,
    ) where
        E: Eq + Hash + Clone,
        F: FnMut(&E, &str, &str) -> bool,
    {
        if node == hierarchy.top_node() || self.inconsistent {
            for individual in all_individuals {
                result.insert(individual.clone());
            }
            return;
        }
        let role = hierarchy.node(node).representative().clone();
        let possible_successors: Vec<String> = self
            .node_to_element
            .get(&node)
            .and_then(|e| e.possible_relations().get(subject))
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_default();
        let parents: Vec<NodeRef> = hierarchy.node(node).parent_nodes().iter().copied().collect();
        for successor in possible_successors {
            if is_role_instance(&role, subject, &successor) {
                self.element_mut(node).set_to_known(subject, &successor);
            } else {
                for &parent in &parents {
                    self.element_mut(parent).add_possible(subject, &successor);
                }
            }
        }
        if let Some(known) =
            self.node_to_element.get(&node).and_then(|e| e.known_relations().get(subject))
        {
            for successor in known {
                if all_individuals.contains(successor) {
                    result.insert(successor.clone());
                }
            }
        }
        let children: Vec<NodeRef> = hierarchy.node(node).child_nodes().iter().copied().collect();
        for child in children {
            self.collect_object_property_values(
                hierarchy,
                child,
                subject,
                all_individuals,
                is_role_instance,
                result,
            );
        }
    }

    /// `getObjectPropertySubjects(node, object)` (InstanceManager.java:1171-1196):
    /// the subjects related to `object` under the role.
    pub fn get_object_property_subjects<E, F>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        object: &str,
        all_individuals: &HashSet<String>,
        is_role_instance: &mut F,
    ) -> HashSet<String>
    where
        E: Eq + Hash + Clone,
        F: FnMut(&E, &str, &str) -> bool,
    {
        let mut result = HashSet::new();
        self.collect_object_property_subjects(
            hierarchy,
            node,
            object,
            all_individuals,
            is_role_instance,
            &mut result,
        );
        result
    }

    fn collect_object_property_subjects<E, F>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        node: NodeRef,
        object: &str,
        all_individuals: &HashSet<String>,
        is_role_instance: &mut F,
        result: &mut HashSet<String>,
    ) where
        E: Eq + Hash + Clone,
        F: FnMut(&E, &str, &str) -> bool,
    {
        if node == hierarchy.top_node() || self.inconsistent {
            for individual in all_individuals {
                result.insert(individual.clone());
            }
            return;
        }
        let role = hierarchy.node(node).representative().clone();
        // Knowns.
        let known_subjects: Vec<String> = self
            .node_to_element
            .get(&node)
            .map(|e| {
                e.known_relations()
                    .iter()
                    .filter(|(subject, targets)| {
                        all_individuals.contains(subject.as_str()) && targets.contains(object)
                    })
                    .map(|(subject, _)| subject.clone())
                    .collect()
            })
            .unwrap_or_default();
        for subject in known_subjects {
            result.insert(subject);
        }
        // Possibles. Java iterates *all* possible-subject keys; the `else`
        // branch (push `(subject, object)` to every parent's possibles) fires
        // for any subject failing the relevance / target-contains-object /
        // role-instance test, so the relevance and contains-object checks must
        // stay inside the loop rather than pre-filtering the iteration set.
        let possible_subjects: Vec<(String, bool)> = self
            .node_to_element
            .get(&node)
            .map(|e| {
                e.possible_relations()
                    .iter()
                    .map(|(subject, targets)| (subject.clone(), targets.contains(object)))
                    .collect()
            })
            .unwrap_or_default();
        let parents: Vec<NodeRef> = hierarchy.node(node).parent_nodes().iter().copied().collect();
        for (subject, contains_object) in possible_subjects {
            if all_individuals.contains(subject.as_str())
                && contains_object
                && is_role_instance(&role, &subject, object)
            {
                self.element_mut(node).set_to_known(&subject, object);
                result.insert(subject);
            } else {
                for &parent in &parents {
                    self.element_mut(parent).add_possible(&subject, object);
                }
            }
        }
        let children: Vec<NodeRef> = hierarchy.node(node).child_nodes().iter().copied().collect();
        for child in children {
            self.collect_object_property_subjects(
                hierarchy,
                child,
                object,
                all_individuals,
                is_role_instance,
                result,
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hierarchy::build_hierarchy;

    #[test]
    fn atomic_concept_element_known_possible() {
        let mut element = AtomicConceptElement::default();
        assert!(element.add_possible("a"));
        assert!(element.is_possible("a"));
        assert!(!element.is_known("a"));
        element.set_to_known("a");
        assert!(element.is_known("a"));
        assert!(!element.is_possible("a"));
        assert!(!element.has_possibles());
    }

    #[test]
    fn role_element_known_possible() {
        let mut manager = RoleElementManager::new();
        let element = manager.get_role_element("r");
        assert!(element.add_possible("a", "b"));
        assert!(element.is_possible("a", "b"));
        assert!(!element.is_known("a", "b"));
        element.set_to_known("a", "b");
        assert!(element.is_known("a", "b"));
        assert!(!element.is_possible("a", "b"));
        assert!(!element.has_possibles());
        assert!(element.remove_known("a", "b"));
        assert!(!element.is_known("a", "b"));
    }

    #[test]
    fn instance_manager_get_types() {
        // Hierarchy: Dog ⊑ Animal (subsumers Dog:{Dog,Animal,top}, Animal:{Animal,top}).
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top", ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "Animal", "Dog", "bottom"].into_iter().collect());
        subsumers.insert("Animal", ["Animal", "top"].into_iter().collect());
        subsumers.insert("Dog", ["Dog", "Animal", "top"].into_iter().collect());
        let hierarchy = build_hierarchy("top", "bottom", subsumers);

        let dog_node = hierarchy.node_for_element(&"Dog").unwrap();
        let animal_node = hierarchy.node_for_element(&"Animal").unwrap();

        // rex is a Dog (hence an Animal). The oracle says rex is a Dog and an
        // Animal but not bottom. The bottom-most relevant node is seeded possible
        // (the read-off side of HermiT), as the oracle only runs for possibles.
        let mut manager: InstanceManager<&str> = InstanceManager::new();
        manager.add_possible(dog_node, "rex");
        let direct = manager.get_types(&hierarchy, "rex", true, |c| {
            *c == "Dog" || *c == "Animal" || *c == "top"
        });
        // Direct type is Dog (the most specific), not Animal.
        assert!(direct.contains(&dog_node));
        assert!(!direct.contains(&animal_node));

        let mut manager2: InstanceManager<&str> = InstanceManager::new();
        manager2.add_possible(dog_node, "rex");
        let all = manager2.get_types(&hierarchy, "rex", false, |c| {
            *c == "Dog" || *c == "Animal" || *c == "top"
        });
        // All types include Dog and Animal.
        assert!(all.contains(&dog_node));
        assert!(all.contains(&animal_node));
    }

    fn dog_animal_hierarchy() -> Hierarchy<&'static str> {
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top", ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "Animal", "Dog", "bottom"].into_iter().collect());
        subsumers.insert("Animal", ["Animal", "top"].into_iter().collect());
        subsumers.insert("Dog", ["Dog", "Animal", "top"].into_iter().collect());
        build_hierarchy("top", "bottom", subsumers)
    }

    #[test]
    fn seeded_manager_known_read_off_and_types() {
        // Read off rex's KNOWN memberships {Dog, Animal} (deterministic) directly,
        // with no realize needed (no possibles).
        let hierarchy = dog_animal_hierarchy();
        let dog_node = hierarchy.node_for_element(&"Dog").unwrap();
        let animal_node = hierarchy.node_for_element(&"Animal").unwrap();

        let mut manager = SeededClassInstanceManager::new();
        manager.seed_same_as(&["rex".to_string()], &[]);
        let labels = vec![
            ReadOffConcept { concept_iri: "Dog".to_string(), known: true },
            ReadOffConcept { concept_iri: "Animal".to_string(), known: true },
        ];
        manager.read_off_types("rex", &labels, |iri| hierarchy.node_for_element(&iri));
        manager.seed_top_known(hierarchy.top_node(), "rex");
        // No possibles -> realize is a no-op; oracle must never be called.
        manager.realize(&hierarchy, |_c: &&str, _i| panic!("oracle must not run for knowns"));

        let direct = manager.get_types_of(&hierarchy, "rex", true);
        assert!(direct.contains(&dog_node));
        assert!(!direct.contains(&animal_node));

        let mut individuals = HashSet::new();
        individuals.insert("rex".to_string());
        assert!(manager
            .get_instances(&hierarchy, dog_node, false, &individuals)
            .contains("rex"));
        assert!(manager
            .get_instances(&hierarchy, animal_node, false, &individuals)
            .contains("rex"));
        // Direct instance of Dog (not Animal).
        assert!(manager
            .get_instances(&hierarchy, dog_node, true, &individuals)
            .contains("rex"));
        assert!(!manager
            .get_instances(&hierarchy, animal_node, true, &individuals)
            .contains("rex"));
    }

    #[test]
    fn seeded_manager_possible_confirmed_and_refuted() {
        // x is a POSSIBLE Dog. realize confirms it for `confirm` and refutes it for
        // `refute`, matching what an oracle would decide.
        let hierarchy = dog_animal_hierarchy();
        let dog_node = hierarchy.node_for_element(&"Dog").unwrap();

        // Confirmed: realize promotes the possible to known at Dog.
        let mut confirm = SeededClassInstanceManager::new();
        confirm.seed_same_as(&["x".to_string()], &[]);
        confirm.read_off_types(
            "x",
            &[ReadOffConcept { concept_iri: "Dog".to_string(), known: false }],
            |iri| hierarchy.node_for_element(&iri),
        );
        confirm.seed_top_known(hierarchy.top_node(), "x");
        assert!(confirm.reading_off_found_possible());
        confirm.realize(&hierarchy, |c: &&str, _i| *c == "Dog");
        assert!(confirm.get_types_of(&hierarchy, "x", false).contains(&dog_node));

        // Refuted: realize drops the possible and pushes it up; Dog is not a type.
        let mut refute = SeededClassInstanceManager::new();
        refute.seed_same_as(&["x".to_string()], &[]);
        refute.read_off_types(
            "x",
            &[ReadOffConcept { concept_iri: "Dog".to_string(), known: false }],
            |iri| hierarchy.node_for_element(&iri),
        );
        refute.seed_top_known(hierarchy.top_node(), "x");
        refute.realize(&hierarchy, |_c: &&str, _i| false);
        assert!(!refute.get_types_of(&hierarchy, "x", false).contains(&dog_node));
    }

    #[test]
    fn seeded_manager_same_as_grouping() {
        let mut manager = SeededClassInstanceManager::new();
        // Deterministic same-as a~b; c stands alone.
        manager.seed_same_as(
            &["a".to_string(), "b".to_string(), "c".to_string()],
            &[("a".to_string(), "b".to_string(), true)],
        );
        assert!(manager.is_same_individual("a", "b"));
        assert!(manager.is_same_individual("b", "a"));
        assert!(!manager.is_same_individual("a", "c"));
        assert_eq!(manager.same_as_individuals("a"), vec!["a".to_string(), "b".to_string()]);
        assert_eq!(manager.same_as_individuals("c"), vec!["c".to_string()]);
    }
}
