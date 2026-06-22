// Port of org.semanticweb.HermiT.hierarchy.QuasiOrderClassification.
//
// HermiT's "quasi-order" classifier builds a concept hierarchy with two graphs:
//   * `known_subsumptions`   -- subsumptions established for certain, and
//   * `possible_subsumptions` -- candidate subsumptions read off a model that
//                                still need an explicit subsumption test.
// It seeds the known graph from told subsumers, then uses a "leaf-node strategy"
// (build a model for each concept, read its deterministic subsumers as known and
// its remaining label as possible, propagate unsatisfiability downward), and
// finally resolves the leftover possible subsumptions with the enhanced-traversal
// search over a small hierarchy of the unknown possible subsumers. The result is
// the transitively reduced hierarchy.
//
// HermiT's original works directly against the tableau (extension tables, node
// labels, dependency sets). Just like the `InstanceManager` port, this version
// is parameterized by an oracle so the algorithm is decoupled from the engine and
// testable in isolation:
//   * `build_model(concept)` returns `None` if `concept` is unsatisfiable, else
//     the `(known_subsumers, possible_subsumers)` read from its model's root node
//     (deterministic label vs. the rest), and
//   * `does_subsume(parent, child)` is the explicit subsumption test.
// Because the per-concept readout already yields each concept's own possible
// subsumers, the driver builds a model for every satisfiable concept rather than
// harvesting cross-node labels (a performance difference only; the resulting
// hierarchy is identical).

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

/// This process's resident-set size in MiB, or `None` when unavailable (non-Linux
/// or unreadable `/proc`). Cheap: one small read + parse. The second
/// whitespace-separated field of `/proc/self/statm` is the resident page count.
fn process_rss_mib() -> Option<usize> {
    let statm = std::fs::read_to_string("/proc/self/statm").ok()?;
    let resident_pages: usize = statm.split_whitespace().nth(1)?.parse().ok()?;
    Some(resident_pages * 4 / 1024) // 4 KiB pages -> MiB
}

/// Total system memory (`MemTotal`) in MiB, or `None` when unavailable.
fn system_total_mib() -> Option<usize> {
    let meminfo = std::fs::read_to_string("/proc/meminfo").ok()?;
    for line in meminfo.lines() {
        if let Some(rest) = line.strip_prefix("MemTotal:") {
            let kib: usize = rest.split_whitespace().next()?.parse().ok()?;
            return Some(kib / 1024);
        }
    }
    None
}

/// Parses a MiB threshold from an environment variable, ignoring empty/garbage.
fn env_mib(name: &str) -> Option<usize> {
    std::env::var(name).ok()?.trim().parse().ok()
}

/// Adaptive cap on the number of concurrent model builds, throttling dispatch
/// when resident memory is high so only one worker saturates a (possibly
/// multi-GB) satisfiability tableau at a time. Below a high-water mark it returns
/// the full worker width; once resident memory crosses the high mark it collapses
/// to 1 and stays there until memory falls back under a low-water mark
/// (hysteresis, so the budget does not oscillate dispatch each class).
///
/// Watermarks default to fractions of total RAM (≈62% high, ≈50% low) and are
/// overridable via `OWLMAKE_CLASSIFY_MEM_HIGH_MIB` / `OWLMAKE_CLASSIFY_MEM_LOW_MIB`.
/// When system memory cannot be read the governor is inert (always full width),
/// preserving the prior behaviour.
struct MemoryGovernor {
    full: usize,
    high_mib: usize,
    low_mib: usize,
    throttled: bool,
    debug: bool,
}

impl MemoryGovernor {
    fn new(full: usize) -> MemoryGovernor {
        let total = system_total_mib();
        let high_mib = env_mib("OWLMAKE_CLASSIFY_MEM_HIGH_MIB")
            .or_else(|| total.map(|t| t * 62 / 100))
            .unwrap_or(usize::MAX);
        let low_mib = env_mib("OWLMAKE_CLASSIFY_MEM_LOW_MIB")
            .or_else(|| total.map(|t| t * 50 / 100))
            .unwrap_or(0);
        MemoryGovernor {
            full: full.max(1),
            high_mib,
            low_mib,
            throttled: false,
            debug: std::env::var_os("HERMIT_DEBUG_TABLEAU").is_some(),
        }
    }

    /// The number of model builds to keep in flight given current memory pressure.
    /// Re-reads RSS each call (once per harvested class — negligible next to a
    /// tableau saturation).
    fn budget(&mut self) -> usize {
        if self.high_mib == usize::MAX {
            return self.full; // governor inert (no system-memory reading)
        }
        let rss = match process_rss_mib() {
            Some(r) => r,
            None => return self.full,
        };
        let was = self.throttled;
        if self.throttled {
            if rss < self.low_mib {
                self.throttled = false;
            }
        } else if rss > self.high_mib {
            self.throttled = true;
        }
        if self.debug && was != self.throttled {
            eprintln!(
                "[mem-governor] {} at rss={}MiB (high={} low={})",
                if self.throttled { "THROTTLE->1" } else { "RELEASE->full" },
                rss,
                self.high_mib,
                self.low_mib,
            );
        }
        if self.throttled {
            1
        } else {
            self.full
        }
    }
}

/// Fallback path only: when the oracle exposes a [`StreamingModelPool`] (the
/// concrete tableau oracle does), the leaf-node strategy runs the barrier-free
/// streaming pipeline in
/// [`try_streaming_leaf_node_strategy`](QuasiOrderClassification::try_streaming_leaf_node_strategy)
/// and this batched-round path is unused. It remains for oracles without a
/// streaming backend (e.g. the in-memory test oracle).
///
/// How many concepts the leaf-node strategy drains from the worklist per round
/// before building their (independent) models together via the oracle's
/// [`build_models_batch`](SubsumptionOracle::build_models_batch). The whole round
/// is one parallel build over a global work queue (continuous work-stealing, no
/// per-N barrier inside the round), so a worker that finishes a cheap model
/// immediately grabs the next concept instead of idling. The harvest of a round's
/// read-offs is serial, confluent, and only ~2% of the time, then the round's
/// buffered read-offs are freed -- so the round size directly bounds peak memory
/// (the count of dense read-offs held at once). It only trades round count (and
/// thus barrier/tail-idle overhead) against that memory bound; it is answer-neutral.
const LEAF_NODE_BATCH_SIZE: usize = 256;

use crate::graph::Graph;
use crate::hierarchy::{
    build_hierarchy_with_monitor, ClassificationProgressMonitor, NoProgressMonitor, Hierarchy,
    NodeRef,
};

/// The read-off of one saturated model, used by the leaf-node strategy.
pub struct ModelReadOff<E> {
    /// `readKnownSubsumersFromRootNode`: the query concept's deterministic
    /// (empty-dependency-set) subsumers, read off the model's root node when the
    /// root was not merged non-deterministically.
    pub query_known: HashSet<E>,
    /// The query concept's possible subsumers. Used only when `node_labels` is
    /// `None` (an oracle, like the role classifier's edge read-off, that does not
    /// expose full node labels for cross-concept harvesting).
    pub query_possible: HashSet<E>,
    /// `updatePossibleSubsumers`: the concept label of every active, unblocked node
    /// in the model. Every concept that appears in a label gets its possible
    /// subsumers harvested (first occurrence) or pruned/intersected (later
    /// occurrences) against the label, so one model build populates the possible
    /// subsumers of many concepts. `None` disables cross-concept harvesting.
    pub node_labels: Option<Vec<HashSet<E>>>,
}

/// The outcome of the batched union test (`isEveryPossibleSubsumerNonSubsumer`).
/// When `subsumed` is true, the witnessing model also yields the query's
/// deterministic known subsumers (`readKnownSubsumersFromRootNode`), which the
/// classifier records and removes from the possible set to avoid redundant
/// pairwise tests. `query_known` is empty (and ignored) when `subsumed` is false.
pub struct UnionTestResult<E> {
    pub subsumed: bool,
    pub query_known: HashSet<E>,
}

/// Everything one `picked` element's resolution reads from the shared graphs,
/// snapshotted by the coordinator so the resolution can run in ISOLATION on a
/// worker thread (no access to the live, mutating classification state). The
/// subsumption tests it runs are pure functions of their concept pair over the
/// read-only TBox, so several pickeds' resolutions run concurrently and their
/// (confluent) deltas are harvested serially -- byte-identical to the one-at-a-time
/// path, the same property the leaf-node strategy relies on.
#[derive(Clone)]
pub struct ResolveTask<E> {
    pub picked: E,
    /// `picked`'s current possible subsumers (already pruned by its known ones).
    pub unknown: HashSet<E>,
    /// `all_known_subsumers(e)` for `e == picked` and every `e` in `unknown`,
    /// snapshotted from the pre-round known graph -- all the reachability the
    /// isolated resolution reads. (An entry may under-approximate a subsumer
    /// discovered mid-resolution whose own subsumers were not snapshotted; that
    /// only costs an extra, correct subsumption test, never a wrong answer.)
    pub known_map: HashMap<E, HashSet<E>>,
}

/// The confluent result of an isolated [`resolve_picked_isolated`]: the
/// `picked ⊑ X` subsumptions it discovered and the witnessing-model labels it
/// produced, for the coordinator to fold into the shared graphs (monotonic known
/// unions + intersective possible prunes -> order-independent final hierarchy).
pub struct ResolveDelta<E> {
    pub picked: E,
    pub new_knowns: Vec<E>,
    pub pruned_labels: Vec<HashSet<E>>,
}

/// Resolve ONE picked element in isolation against a snapshot (`task.known_map`)
/// of the reachability its serial counterpart would read, plus `oracle` for the
/// model builds. Mirrors, step for step, the serial trio
/// `is_every_possible_subsumer_non_subsumer` -> `build_hierarchy_of_unknown_possible`
/// -> `check_unknown_subsumers_using_enhanced_traversal`, but accumulates the
/// discovered knowns and witnessing labels into a [`ResolveDelta`] instead of
/// mutating shared state. CLASS MODE ONLY (no inverse-concept mirroring); the
/// classifier runs the serial path when inverses are present.
pub fn resolve_picked_isolated<E, O>(
    task: ResolveTask<E>,
    top: &E,
    bottom: &E,
    elements: &HashSet<E>,
    oracle: &mut O,
) -> ResolveDelta<E>
where
    E: Eq + Hash + Clone,
    O: SubsumptionOracle<E>,
{
    let ResolveTask { picked, unknown, known_map } = task;
    let mut delta = ResolveDelta {
        picked: picked.clone(),
        new_knowns: Vec::new(),
        pruned_labels: Vec::new(),
    };
    // Local mirror of the shared graphs, restricted to `picked`.
    let mut known_of_picked: HashSet<E> = known_map.get(&picked).cloned().unwrap_or_default();
    let mut possible_of_picked: HashSet<E> = unknown;

    // `addKnownSubsumption(picked, sup)`, keeping `known_of_picked` transitively
    // closed via the snapshot (`sup`'s own subsumers don't change during this
    // picked's resolution, so the pre-round snapshot is exact for them).
    fn add_known<E: Eq + Hash + Clone>(
        sup: &E,
        known_map: &HashMap<E, HashSet<E>>,
        known_of_picked: &mut HashSet<E>,
        new_knowns: &mut Vec<E>,
    ) {
        if known_of_picked.insert(sup.clone()) {
            new_knowns.push(sup.clone());
        }
        if let Some(s) = known_map.get(sup) {
            known_of_picked.extend(s.iter().cloned());
        }
    }

    // --- isEveryPossibleSubsumerNonSubsumer (on the current possible set) ---
    if possible_of_picked.len() > 2 && possible_of_picked.len() < 7 {
        if let Some(result) = oracle.is_subsumed_by_union(&picked, &possible_of_picked) {
            if result.subsumed {
                for sup in &result.query_known {
                    if elements.contains(sup) {
                        add_known(sup, &known_map, &mut known_of_picked, &mut delta.new_knowns);
                    }
                }
                possible_of_picked.retain(|s| !known_of_picked.contains(s));
            }
            if !result.subsumed {
                // No candidate subsumes `picked`; skip the traversal entirely.
                return delta;
            }
        }
    }
    if possible_of_picked.is_empty() {
        return delta;
    }

    // --- buildHierarchyOfUnknownPossible + checkUnknownSubsumersUsingEnhancedTraversal ---
    let small = build_small_hierarchy(&possible_of_picked, &known_map, top, bottom);
    let start = small.top_node();
    let mut visited: HashSet<NodeRef> = HashSet::new();
    visited.insert(start);
    let mut to_process: VecDeque<NodeRef> = VecDeque::new();
    to_process.push_back(start);
    while let Some(current) = to_process.pop_front() {
        let children: Vec<NodeRef> = small.node(current).child_nodes().iter().copied().collect();
        for child in children {
            if visited.contains(&child) {
                continue;
            }
            let element = small.node(child).representative().clone();
            let subsumes = if known_of_picked.contains(&element) {
                true
            } else if !possible_of_picked.contains(&element) {
                false
            } else {
                let (subsumed, read_off) = oracle.does_subsume_with_read_off(&element, &picked);
                if let Some(read_off) = read_off {
                    for sup in &read_off.query_known {
                        if elements.contains(sup) {
                            add_known(sup, &known_map, &mut known_of_picked, &mut delta.new_knowns);
                        }
                    }
                    if let Some(node_labels) = read_off.node_labels {
                        for label in &node_labels {
                            // prunePossibleSubsumers' effect on `picked`'s own set
                            // (the global effect on other concepts is replayed by
                            // the coordinator from `pruned_labels`).
                            if label.contains(&picked) {
                                possible_of_picked.retain(|s| label.contains(s));
                            }
                        }
                        delta.pruned_labels.extend(node_labels);
                    }
                }
                possible_of_picked.retain(|s| !known_of_picked.contains(s));
                subsumed
            };
            if subsumes {
                add_known(&element, &known_map, &mut known_of_picked, &mut delta.new_knowns);
                let equivalents = small.node(child).equivalent_elements().clone();
                for e in &equivalents {
                    add_known(e, &known_map, &mut known_of_picked, &mut delta.new_knowns);
                }
                if visited.insert(child) {
                    to_process.push_back(child);
                }
            }
            visited.insert(child);
        }
    }
    delta
}

/// `buildHierarchyOfUnknownPossible` over a snapshot: the small hierarchy of the
/// unknown possible subsumers (plus top and bottom), ordered by the snapshotted
/// known subsumption. Free-function form of the method, reading `known_map`
/// instead of the live known graph so it runs on a worker.
fn build_small_hierarchy<E: Eq + Hash + Clone>(
    unknown: &HashSet<E>,
    known_map: &HashMap<E, HashSet<E>>,
    top: &E,
    bottom: &E,
) -> Hierarchy<E> {
    let empty: HashSet<E> = HashSet::new();
    let mut small: Graph<E> = Graph::new();
    for u0 in unknown {
        small.add_edge(bottom.clone(), u0.clone());
        small.add_edge(u0.clone(), top.clone());
        let known = known_map.get(u0).unwrap_or(&empty);
        for u1 in unknown {
            if known.contains(u1) {
                small.add_edge(u0.clone(), u1.clone());
            }
        }
    }
    let mut with_top_bottom = unknown.clone();
    with_top_bottom.insert(bottom.clone());
    with_top_bottom.insert(top.clone());
    // build_transitively_reduced_hierarchy(small, with_top_bottom).
    let mut subsumers: HashMap<E, HashSet<E>> = HashMap::new();
    for element in &with_top_bottom {
        let mut extended = small.get_successors(element);
        extended.insert(top.clone());
        extended.insert(element.clone());
        subsumers.insert(element.clone(), extended);
    }
    subsumers.insert(bottom.clone(), with_top_bottom.clone());
    build_hierarchy_with_monitor(top.clone(), bottom.clone(), subsumers, &mut NoProgressMonitor)
}

/// A persistent streaming pool of model-building workers, owned for the duration
/// of the leaf-node strategy. The coordinator (the classifier thread, which owns
/// ALL mutable classification state) drives it as a continuous pipeline: it
/// [`dispatch`](StreamingModelPool::dispatch)es a concept to a free worker and
/// later [`recv`](StreamingModelPool::recv)s ONE completed read-off, in whatever
/// order it finishes. There is no per-round barrier: a slow dense model occupies
/// exactly one worker while the others keep building and completing.
///
/// RAM is bounded by the in-flight count the coordinator maintains (at most
/// `worker_count` concurrent tableaux) plus a tiny results channel -- the pool
/// holds NO reorder buffer (results are handed back in arrival order and harvested
/// immediately), so the streaming design never accumulates completed read-offs.
pub trait StreamingModelPool<E> {
    /// Hand `concept` to the pool's work channel for a worker to build. Returns
    /// without blocking on the build. The coordinator only calls this while its
    /// in-flight count is below the worker count, so the bounded work channel
    /// never backs up more than the workers can drain.
    fn dispatch(&mut self, concept: E);
    /// Block until ONE dispatched build completes, returning its `(concept,
    /// read_off)` (`read_off` is `None` if the concept is unsatisfiable). Results
    /// arrive in completion order; the harvest the coordinator applies is
    /// confluent, so the final hierarchy is order-independent. Returns `None` only
    /// if the pool has been drained and all workers have exited (never happens
    /// while in-flight > 0).
    fn recv(&mut self) -> Option<(E, Option<ModelReadOff<E>>)>;
    /// How many concurrent builds the pool can run -- the coordinator keeps exactly
    /// this many in flight (one per worker), so no worker idles and RAM stays
    /// bounded by this many concurrent tableaux.
    fn worker_count(&self) -> usize;
}

/// A persistent pool of resolution workers, the resolution-phase analogue of
/// [`StreamingModelPool`]. The coordinator (which owns all mutable classification
/// state) [`dispatch`](ResolutionPool::dispatch)es a [`ResolveTask`] (a picked
/// element plus the reachability snapshot its isolated resolution reads) and later
/// [`recv`](ResolutionPool::recv)s ONE completed [`ResolveDelta`], in completion
/// order. Continuous dispatch (each task snapshotted at dispatch time, after prior
/// deltas were harvested) keeps the build count near the serial path's while the
/// persistent workers avoid any per-round setup. RAM is bounded by the in-flight
/// count the coordinator maintains (`<= worker_count`).
pub trait ResolutionPool<E> {
    fn dispatch(&mut self, task: ResolveTask<E>);
    fn recv(&mut self) -> Option<ResolveDelta<E>>;
    fn worker_count(&self) -> usize;
}

/// The model/subsumption oracle the classifier runs against (the tableau in
/// HermiT). `E` is the element type (atomic concepts, identified by value).
pub trait SubsumptionOracle<E> {
    /// `buildModelForConcept` + `readKnownSubsumersFromRootNode` +
    /// `updatePossibleSubsumers`: `None` if `concept` is unsatisfiable, else the
    /// model read-off (query's known subsumers, and either the query's possible
    /// subsumers or the full node labels for cross-concept harvesting).
    fn build_model(&mut self, concept: &E) -> Option<ModelReadOff<E>>;
    /// Build the models of a *batch* of independent concepts, returning the
    /// read-offs in the same order as `concepts`. The model builds are mutually
    /// independent (each saturates its own tableau over the read-only TBox), so an
    /// oracle backed by a thread-safe engine runs them in parallel across a fixed
    /// worker pool fed by a single global work queue (a worker that finishes a cheap
    /// model immediately steals the next concept); the default runs them serially
    /// via [`build_model`](Self::build_model). The caller harvests the returned
    /// read-offs into the shared classification state SERIALLY in a deterministic
    /// order, so the result is byte-identical to the one-at-a-time path -- only the
    /// (independent) model construction is parallelised.
    fn build_models_batch(&mut self, concepts: &[E]) -> Vec<Option<ModelReadOff<E>>> {
        concepts.iter().map(|c| self.build_model(c)).collect()
    }
    /// Open a [`StreamingModelPool`] of persistent workers for the leaf-node
    /// strategy, or `None` if this oracle has no parallel streaming backend (the
    /// caller then falls back to the serial [`build_model`](Self::build_model)
    /// path). The pool borrows `self` for its lifetime; the coordinator drives it
    /// to completion and drops it (joining the workers) before any other oracle
    /// method is called. The worker model builds are mutually independent, so the
    /// streamed read-offs are byte-identical to the serial ones.
    fn streaming_pool<'p>(&'p mut self) -> Option<Box<dyn StreamingModelPool<E> + 'p>> {
        None
    }
    /// `Relation.doesSubsume`: the explicit subsumption test `parent ⊒ child`.
    fn does_subsume(&mut self, parent: &E, child: &E) -> bool;
    /// `Relation.doesSubsume` together with the model read-off it harvests:
    /// `readKnownSubsumersFromRootNode` (the deterministic subsumers of `child`,
    /// returned in [`ModelReadOff::query_known`]) and, when `child` is NOT subsumed
    /// by `parent`, the witnessing model's node labels for `prunePossibleSubsumers`
    /// (returned in [`ModelReadOff::node_labels`]). The boolean is the subsumption
    /// result; the read-off is `None` when `parent ⊒ child` (the test is
    /// unsatisfiable, so no model exists to harvest). The default implementation
    /// performs no harvesting (for oracles that do not expose model internals).
    fn does_subsume_with_read_off(
        &mut self,
        parent: &E,
        child: &E,
    ) -> (bool, Option<ModelReadOff<E>>) {
        (self.does_subsume(parent, child), None)
    }
    /// The batched test of `isEveryPossibleSubsumerNonSubsumer`: whether `child`
    /// is subsumed by the *union* of `candidates` (one satisfiability test). When
    /// it is NOT subsumed by the union, no candidate individually subsumes it, so
    /// all are non-subsumers. When it IS subsumed, the returned
    /// [`UnionTestResult::query_known`] carries the deterministic subsumers read
    /// off the witnessing model (`readKnownSubsumersFromRootNode`). `None` if the
    /// oracle does not support the batched test (the caller then falls back to the
    /// per-candidate traversal).
    fn is_subsumed_by_union(
        &mut self,
        _child: &E,
        _candidates: &HashSet<E>,
    ) -> Option<UnionTestResult<E>> {
        None
    }
    /// Open a persistent [`ResolutionPool`] for the resolution phase, or `None` if
    /// this oracle has no parallel backend (the caller then runs the serial path).
    /// The workers resolve isolated tasks over the read-only TBox; `top`, `bottom`
    /// and `elements` are the (shared, read-only) classification constants they
    /// need. The pool borrows `self` for its lifetime and is dropped (joining its
    /// workers) before any other oracle method is called.
    fn resolution_pool<'p>(
        &'p mut self,
        _top: &E,
        _bottom: &E,
        _elements: &HashSet<E>,
    ) -> Option<Box<dyn ResolutionPool<E> + 'p>> {
        None
    }
}

/// Port of `QuasiOrderClassification`.
pub struct QuasiOrderClassification<E: Eq + Hash + Clone, O> {
    /// The model/subsumption oracle. Wrapped in `Option` only so the streaming
    /// leaf-node strategy can `take()` it (to open a pool that borrows it
    /// exclusively) while still mutating the rest of `self`'s classification state,
    /// then restore it; it is `Some` everywhere else (the accessors unwrap it).
    oracle: Option<O>,
    top_element: E,
    bottom_element: E,
    elements: HashSet<E>,
    known_subsumptions: Graph<E>,
    possible_subsumptions: Graph<E>,
    /// Port of `QuasiOrderClassificationForRoles`: in role mode with inverses,
    /// `inverse_concept[c]` is the element for the inverse of the role `c`
    /// represents. When present, every known / possible subsumption is mirrored
    /// to the inverse concepts (the subclass's `addKnownSubsumption` /
    /// `addPossibleSubsumption` overrides).
    inverse_concept: Option<HashMap<E, E>>,
}

impl<E, O> QuasiOrderClassification<E, O>
where
    E: Eq + Hash + Clone,
    O: SubsumptionOracle<E>,
{
    pub fn new(
        oracle: O,
        top_element: E,
        bottom_element: E,
        elements: HashSet<E>,
    ) -> QuasiOrderClassification<E, O> {
        QuasiOrderClassification {
            oracle: Some(oracle),
            top_element,
            bottom_element,
            elements,
            known_subsumptions: Graph::new(),
            possible_subsumptions: Graph::new(),
            inverse_concept: None,
        }
    }

    /// The oracle, which is `Some` outside the streaming-pipeline window.
    fn oracle_mut(&mut self) -> &mut O {
        self.oracle.as_mut().expect("oracle present outside the streaming window")
    }

    /// Port of `QuasiOrderClassificationForRoles`'s constructor: the role
    /// classifier. `inverse_concept` maps each role-concept to the concept of its
    /// inverse role; when the ontology has inverses this drives the mirroring of
    /// every subsumption onto the inverse concepts. Pass `None` for no inverses.
    pub fn new_for_roles(
        oracle: O,
        top_element: E,
        bottom_element: E,
        elements: HashSet<E>,
        inverse_concept: Option<HashMap<E, E>>,
    ) -> QuasiOrderClassification<E, O> {
        QuasiOrderClassification {
            oracle: Some(oracle),
            top_element,
            bottom_element,
            elements,
            known_subsumptions: Graph::new(),
            possible_subsumptions: Graph::new(),
            inverse_concept,
        }
    }

    /// `m_conceptsForRoles.get(m_rolesForConcepts.get(concept).getInverse())`:
    /// the concept of the inverse role, in role mode with inverses.
    fn inverse_of(&self, concept: &E) -> Option<E> {
        self.inverse_concept.as_ref().and_then(|map| map.get(concept).cloned())
    }

    /// Fold one isolated resolution's confluent delta into the shared graphs,
    /// exactly as the serial per-picked body's mutations would: record the
    /// discovered `picked ⊑ X` knowns, replay the witnessing-model prunes onto
    /// every concept's possibles, then clear `picked`'s possibles.
    fn harvest_resolve_delta(&mut self, delta: ResolveDelta<E>) {
        let ResolveDelta { picked, new_knowns, pruned_labels } = delta;
        for sup in &new_knowns {
            self.add_known_subsumption(&picked, sup);
        }
        if !pruned_labels.is_empty() {
            self.prune_possible_subsumers(&pruned_labels);
        }
        self.possible_subsumptions.clear_successors(&picked);
    }

    /// Resolve ONE picked element in place against the live graphs (the serial
    /// path): the union pre-test, then the enhanced traversal over its unknown
    /// possible subsumers, then clear its possibles.
    fn resolve_one_picked(&mut self, picked: &E) {
        let unknown_possible = self.possible_subsumptions.get_successors(picked);
        if !self.is_every_possible_subsumer_non_subsumer(&unknown_possible, picked) {
            let unknown_possible = self.possible_subsumptions.get_successors(picked);
            if !unknown_possible.is_empty() {
                let small = self.build_hierarchy_of_unknown_possible(&unknown_possible);
                self.check_unknown_subsumers_using_enhanced_traversal(
                    &small,
                    small.top_node(),
                    picked,
                );
            }
        }
        self.possible_subsumptions.clear_successors(picked);
    }

    /// Snapshot `picked`'s resolution inputs from the current graphs into a
    /// [`ResolveTask`] a worker can resolve in isolation.
    fn build_resolve_task(&self, picked: &E) -> ResolveTask<E> {
        let unknown = self.possible_subsumptions.get_successors(picked);
        let mut known_map: HashMap<E, HashSet<E>> = HashMap::new();
        for e in unknown.iter().chain(std::iter::once(picked)) {
            if !known_map.contains_key(e) {
                known_map.insert(e.clone(), self.all_known_subsumers(e));
            }
        }
        ResolveTask { picked: picked.clone(), unknown, known_map }
    }

    /// Resolve the possible-subsumer phase across the oracle's persistent
    /// [`ResolutionPool`], returning `false` (so the caller runs the serial path)
    /// if the oracle has no pool or this is role mode. The coordinator keeps the
    /// pool full (`<= worker_count` in flight): it scans `unclassified` forward,
    /// pruning each element by its known subsumers, dispatching the non-empty ones
    /// (snapshotting their inputs at dispatch, AFTER prior deltas were harvested)
    /// and dropping the empty ones; it harvests each completed delta as it arrives,
    /// which prunes/known-marks the not-yet-dispatched elements. Because every
    /// element is either dispatched (resolved) or found empty (already fully known)
    /// exactly once, and the harvest folds are confluent, the result is
    /// byte-identical to the serial path -- only the (independent) searches run
    /// concurrently. Role mode keeps the serial path (the isolated resolver does
    /// not replicate inverse-concept mirroring).
    fn try_streaming_resolution<M>(
        &mut self,
        unclassified: &mut Vec<E>,
        monitor: &mut M,
        resolve_total: usize,
    ) -> bool
    where
        M: ClassificationProgressMonitor<E> + ?Sized,
    {
        if self.inverse_concept.is_some() {
            return false;
        }
        let mut oracle = self.oracle.take().expect("oracle present in resolution");
        let used = {
            match oracle.resolution_pool(
                &self.top_element,
                &self.bottom_element,
                &self.elements,
            ) {
                None => false,
                Some(mut pool) => {
                    let worker_count = pool.worker_count().max(1);
                    let mut in_flight = 0usize;
                    let mut cursor = 0usize;
                    let mut resolved = 0usize;
                    loop {
                        // Keep the pool full: dispatch the next not-yet-empty pickeds.
                        while in_flight < worker_count {
                            let mut picked: Option<E> = None;
                            while cursor < unclassified.len() {
                                let element = unclassified[cursor].clone();
                                cursor += 1;
                                let known = self.all_known_subsumers(&element);
                                self.possible_subsumptions.remove_successors(&element, &known);
                                if !self.possible_subsumptions.successors_is_empty(&element) {
                                    picked = Some(element);
                                    break;
                                }
                                // else: every possible subsumer is known -> classified.
                            }
                            match picked {
                                Some(p) => {
                                    let task = self.build_resolve_task(&p);
                                    pool.dispatch(task);
                                    in_flight += 1;
                                }
                                None => break,
                            }
                        }
                        if in_flight == 0 {
                            break;
                        }
                        let delta = match pool.recv() {
                            Some(d) => d,
                            None => break,
                        };
                        in_flight -= 1;
                        resolved += 1;
                        monitor.classification_progress(
                            resolve_total.saturating_sub(unclassified.len().saturating_sub(resolved)),
                            resolve_total,
                        );
                        self.harvest_resolve_delta(delta);
                    }
                    drop(pool);
                    true
                }
            }
        };
        self.oracle = Some(oracle);
        used
    }

    /// `getAllKnownSubsumers`.
    fn all_known_subsumers(&self, child: &E) -> HashSet<E> {
        self.known_subsumptions.get_reachable_successors(child)
    }
    /// `addKnownSubsumption` (mirroring to the inverse concepts in role mode).
    fn add_known_subsumption(&mut self, sub: &E, sup: &E) {
        self.known_subsumptions.add_edge(sub.clone(), sup.clone());
        if let (Some(sub_inv), Some(sup_inv)) = (self.inverse_of(sub), self.inverse_of(sup)) {
            self.known_subsumptions.add_edge(sub_inv, sup_inv);
        }
    }
    /// `addKnownSubsumptions`: adds the edges directly. Unlike the singular
    /// `addKnownSubsumption`, this is *not* overridden for roles, so it does not
    /// mirror to the inverse concepts (matching Java's plural variant).
    fn add_known_subsumptions(&mut self, sub: &E, sups: &HashSet<E>) {
        self.known_subsumptions.add_edges(sub.clone(), sups);
    }
    /// `addPossibleSubsumption` (mirroring to the inverse concepts in role mode).
    fn add_possible_subsumption(&mut self, sub: &E, sup: &E) {
        self.possible_subsumptions.add_edge(sub.clone(), sup.clone());
        if let (Some(sub_inv), Some(sup_inv)) = (self.inverse_of(sub), self.inverse_of(sup)) {
            self.possible_subsumptions.add_edge(sub_inv, sup_inv);
        }
    }
    /// `isUnsatisfiable`.
    fn is_unsatisfiable(&self, concept: &E) -> bool {
        self.known_subsumptions.successor_contains(concept, &self.bottom_element)
    }
    /// `makeConceptUnsatisfiable`.
    fn make_concept_unsatisfiable(&mut self, concept: &E) {
        let bottom = self.bottom_element.clone();
        self.add_known_subsumption(concept, &bottom);
        self.possible_subsumptions.clear_successors(concept);
    }
    /// `conceptHasBeenProcessedAlready`.
    fn concept_has_been_processed_already(&self, concept: &E) -> bool {
        !self.possible_subsumptions.successors_is_empty(concept)
            || self.is_unsatisfiable(concept)
    }

    /// `initialiseKnownSubsumptionsUsingToldSubsumers`: seed the known graph with
    /// told subsumptions `(sub, sup)` (HermiT reads these off the binary DL
    /// clauses; the caller supplies the equivalent pairs).
    pub fn initialise_known_subsumptions_using_told_subsumers(&mut self, told: &[(E, E)]) {
        for (sub, sup) in told {
            if self.elements.contains(sub) && self.elements.contains(sup) {
                self.add_known_subsumption(sub, sup);
            }
        }
    }

    /// Port of `QuasiOrderClassificationForRoles.initialiseKnownSubsumptionsUsingToldSubsumers`:
    /// seed the known graph from told role inclusions. Each told inclusion is
    /// `(body_concept, head_concept, args_differ)`: when the body and head atoms'
    /// first arguments differ (`r → s⁻`), the inverse of the body concept is the
    /// sub-concept; otherwise the body concept is. `add_known_subsumption` then
    /// mirrors onto the inverse concepts as needed.
    pub fn initialise_known_subsumptions_for_roles(&mut self, told: &[(E, E, bool)]) {
        for (body_concept, head_concept, args_differ) in told {
            if !self.elements.contains(body_concept) || !self.elements.contains(head_concept) {
                continue;
            }
            if *args_differ {
                if let Some(body_inv) = self.inverse_of(body_concept) {
                    self.add_known_subsumption(&body_inv, head_concept);
                }
            } else {
                self.add_known_subsumption(body_concept, head_concept);
            }
        }
    }

    /// `classify`: the public entry point.
    pub fn classify(self) -> Hierarchy<E> {
        self.classify_with_monitor(&mut NoProgressMonitor)
    }

    /// As [`classify`](Self::classify), but reports progress through a
    /// [`ClassificationProgressMonitor`]: `monitor.element_classified(e)` fires
    /// once per element of the final hierarchy's subsumer graph, matching Java's
    /// `classifyClasses` firing `elementClassified(AtomicConcept)` per concept.
    /// The intermediate hierarchies built during the leaf-node strategy and the
    /// possible-subsumer resolution use a no-op monitor; only the final
    /// transitively-reduced hierarchy is reported, so the monitor sees each
    /// classified element exactly once. Answer-neutral.
    pub fn classify_with_monitor<M>(mut self, monitor: &mut M) -> Hierarchy<E>
    where
        M: ClassificationProgressMonitor<E> + ?Sized,
    {
        let bottom = self.bottom_element.clone();
        self.make_concept_unsatisfiable(&bottom);
        self.update_subsumptions_using_leaf_node_strategy(monitor);

        // Keep only genuinely-unknown possible subsumptions per element.
        let mut unclassified: Vec<E> = Vec::new();
        let elements: Vec<E> = self.elements.iter().cloned().collect();
        for element in &elements {
            if !self.is_unsatisfiable(element) {
                let known = self.all_known_subsumers(element);
                self.possible_subsumptions.remove_successors(element, &known);
                if !self.possible_subsumptions.successors_is_empty(element) {
                    unclassified.push(element.clone());
                }
            }
        }

        // Resolve the remaining possible subsumptions. Report progress as the
        // unresolved set shrinks (continuing the bar past the leaf-node phase).
        //
        // This phase is the second half of classification time, and each picked's
        // resolution is an independent search whose subsumption tests are pure
        // functions over the read-only TBox. When the oracle exposes a parallel
        // `resolution_pool`, the pickeds are resolved across a persistent worker
        // pool, each task snapshotting the (continuously updated) graphs at dispatch
        // -> confluent, byte-identical to the serial path. Without a pool (test
        // oracles / role mode) the original serial loop runs verbatim.
        let resolve_total = self.elements.len();
        if !self.try_streaming_resolution(&mut unclassified, monitor, resolve_total) {
            while !unclassified.is_empty() {
                monitor.classification_progress(
                    resolve_total.saturating_sub(unclassified.len()),
                    resolve_total,
                );
                let mut picked: Option<E> = None;
                let mut classified: HashSet<E> = HashSet::new();
                for element in &unclassified {
                    let known = self.all_known_subsumers(element);
                    self.possible_subsumptions.remove_successors(element, &known);
                    if !self.possible_subsumptions.successors_is_empty(element) {
                        picked = Some(element.clone());
                        break;
                    }
                    classified.insert(element.clone());
                }
                unclassified.retain(|e| !classified.contains(e));
                let picked = match picked {
                    Some(p) if unclassified.iter().any(|e| *e == p) => p,
                    _ => {
                        if unclassified.is_empty() {
                            break;
                        }
                        continue;
                    }
                };
                self.resolve_one_picked(&picked);
            }
        }

        self.build_transitively_reduced_hierarchy_with_monitor(
            &self.known_subsumptions.clone(),
            &self.elements.clone(),
            monitor,
        )
    }

    /// `updateSubsumptionsUsingLeafNodeStrategy`: build a model for each not-yet
    /// processed concept (walking up from the bottom node's parents); record its
    /// deterministic subsumers as known and the rest as possible, propagating
    /// unsatisfiability down to descendants.
    fn update_subsumptions_using_leaf_node_strategy<M>(&mut self, monitor: &mut M)
    where
        M: ClassificationProgressMonitor<E> + ?Sized,
    {
        let hierarchy = self.build_transitively_reduced_hierarchy(
            &self.known_subsumptions.clone(),
            &self.elements.clone(),
        );
        let mut to_process: Vec<NodeRef> =
            hierarchy.node(hierarchy.bottom_node()).parent_nodes().iter().copied().collect();
        let mut unsat_nodes: HashSet<NodeRef> = HashSet::new();

        // Coarse progress: one model build per (still-unprocessed) concept is the
        // dominant cost, so report builds against the total concept count.
        let total = self.elements.len();
        let mut built = 0usize;

        // Streaming pipeline (preferred): a persistent worker pool + this thread as
        // the single-threaded coordinator that owns ALL mutable classification
        // state. No per-round barrier -- a slow dense model occupies one worker
        // while the others keep building and completing. The harvest is the EXACT
        // serial logic and is confluent, so the result is byte-identical and
        // order-independent. Falls back to the batched-round path below when the
        // oracle exposes no streaming backend (e.g. the in-memory test oracle).
        if self.try_streaming_leaf_node_strategy(&hierarchy, &mut to_process, &mut unsat_nodes, &mut built, total, monitor) {
            return;
        }

        // The model builds for distinct concepts are mutually independent (each
        // saturates its own tableau over the read-only TBox), so we drain the
        // worklist in rounds, build each round's models in parallel via the oracle's
        // `build_models_batch` (a thread-safe oracle keeps a worker pool saturated
        // over the whole round), then harvest the read-offs into the shared
        // classification state SERIALLY in a deterministic order. The harvest is
        // confluent -- `updatePossibleSubsumers` intersects a concept's possible set
        // with every label it appears in (order-independent), and the known-subsumer
        // / unsat-propagation updates are pure set operations -- so the result is
        // byte-identical to the one-at-a-time path. The round is sorted by
        // representative concept (NodeRef order = concept identity within one
        // hierarchy) before harvesting, fixing the order so runs are reproducible.
        //
        // Because a round builds models for several concepts at once, a concept may
        // be made unsatisfiable (and thus "processed") by an earlier sibling's
        // unsat-propagation in the same round *after* its model was already built;
        // its now-stale read-off is dropped at harvest time by the same
        // `concept_has_been_processed_already` guard the serial loop applied before
        // each build. The only cost is a few redundant builds; the answer is unchanged.
        while !to_process.is_empty() {
            // Drain a round of distinct, not-yet-processed nodes (deduped so a
            // concept is never built twice in one round).
            let mut batch_nodes: Vec<NodeRef> = Vec::new();
            let mut seen_in_batch: HashSet<NodeRef> = HashSet::new();
            while let Some(node) = to_process.pop() {
                let concept = hierarchy.node(node).representative().clone();
                if self.concept_has_been_processed_already(&concept) {
                    continue;
                }
                if seen_in_batch.insert(node) {
                    batch_nodes.push(node);
                }
                if batch_nodes.len() >= LEAF_NODE_BATCH_SIZE {
                    break;
                }
            }
            if batch_nodes.is_empty() {
                continue;
            }
            // Deterministic harvest order: sort by representative concept.
            batch_nodes.sort_unstable();
            let batch_concepts: Vec<E> = batch_nodes
                .iter()
                .map(|&n| hierarchy.node(n).representative().clone())
                .collect();
            let read_offs = self.oracle_mut().build_models_batch(&batch_concepts);

            for (current_node, (current_concept, model)) in
                batch_nodes.into_iter().zip(batch_concepts.into_iter().zip(read_offs))
            {
                // Re-apply the serial loop's skip: a sibling harvested earlier in
                // this same round may have made this concept unsatisfiable since its
                // build was issued.
                if self.concept_has_been_processed_already(&current_concept) {
                    continue;
                }
                built += 1;
                monitor.classification_progress(built, total);
                self.harvest_leaf_node_result(
                    &hierarchy,
                    current_node,
                    &current_concept,
                    model,
                    &mut to_process,
                    &mut unsat_nodes,
                );
            }
        }
    }

    /// Process ONE leaf-node model read-off into the shared classification state,
    /// exactly as HermiT's serial loop does: an unsatisfiable concept is sent to
    /// bottom and its unsatisfiability is propagated to every descendant (pushing
    /// the freed parents back onto the worklist); a satisfiable concept's
    /// deterministic subsumers are recorded as known and its model's node labels are
    /// harvested into the possible-subsumer sets. Shared by the streaming and
    /// batched-round paths. The caller has already applied the
    /// `concept_has_been_processed_already` skip and the progress tick.
    ///
    /// All mutations here are confluent set operations (`update_possible_subsumers`
    /// intersects, known-subsumer/unsat unions, worklist pushes are deduped by the
    /// processed guard before each build), so processing results in any completion
    /// order yields the same final `known`/`possible` graphs.
    fn harvest_leaf_node_result(
        &mut self,
        hierarchy: &Hierarchy<E>,
        current_node: NodeRef,
        current_concept: &E,
        model: Option<ModelReadOff<E>>,
        to_process: &mut Vec<NodeRef>,
        unsat_nodes: &mut HashSet<NodeRef>,
    ) {
        match model {
            None => {
                self.make_concept_unsatisfiable(current_concept);
                unsat_nodes.insert(current_node);
                for &parent in hierarchy.node(current_node).parent_nodes() {
                    to_process.push(parent);
                }
                // Propagate unsatisfiability to all descendants.
                let mut visited: HashSet<NodeRef> = HashSet::new();
                let mut to_visit: VecDeque<NodeRef> =
                    hierarchy.node(current_node).child_nodes().iter().copied().collect();
                while let Some(child) = to_visit.pop_front() {
                    if visited.insert(child) && !unsat_nodes.contains(&child) {
                        for &grandchild in hierarchy.node(child).child_nodes() {
                            to_visit.push_back(grandchild);
                        }
                        unsat_nodes.insert(child);
                        self.make_concept_unsatisfiable(
                            &hierarchy.node(child).representative().clone(),
                        );
                        to_process.retain(|&n| n != child);
                        for &parent in hierarchy.node(child).parent_nodes() {
                            let parent_concept =
                                hierarchy.node(parent).representative().clone();
                            if !self.concept_has_been_processed_already(&parent_concept) {
                                to_process.push(parent);
                            }
                        }
                    }
                }
            }
            Some(read_off) => {
                // readKnownSubsumersFromRootNode: add each deterministic
                // subsumer via the singular addKnownSubsumption (mirrored to
                // inverses in role mode), not the plural addKnownSubsumptions.
                for sup in &read_off.query_known {
                    if self.elements.contains(sup) {
                        self.add_known_subsumption(current_concept, sup);
                    }
                }
                match read_off.node_labels {
                    // updatePossibleSubsumers: harvest every concept's
                    // possibles from the model's node labels.
                    Some(node_labels) => self.update_possible_subsumers(&node_labels),
                    // No node labels exposed: just the query's own possibles.
                    None => {
                        for sup in read_off.query_possible {
                            if self.elements.contains(&sup) {
                                self.add_possible_subsumption(current_concept, &sup);
                            }
                        }
                    }
                }
            }
        }
    }

    /// The streaming leaf-node strategy: a continuous coordinator/worker pipeline
    /// with NO per-round barrier. Returns `false` if the oracle exposes no
    /// streaming pool (the caller falls back to the batched-round path).
    ///
    /// This thread is the coordinator: it owns all mutable classification state and
    /// the worklist, never blocks on a specific model, and keeps the pipeline full.
    /// Main loop: while in-flight < worker budget and the worklist has a
    /// not-yet-processed concept, dispatch it (in-flight++); then block on the
    /// results channel for ONE completed result, harvest it (the exact serial
    /// logic), in-flight--, and repeat. New worklist entries (freed parents of an
    /// unsatisfiable concept) become dispatchable immediately. Termination: worklist
    /// empty AND in-flight == 0 -> drop the pool (joins workers).
    ///
    /// Determinism: results arrive in completion order, but
    /// [`harvest_leaf_node_result`](Self::harvest_leaf_node_result) is confluent, so
    /// the final `known`/`possible` graphs are order-independent and the built
    /// hierarchy is byte-identical to the serial path.
    fn try_streaming_leaf_node_strategy<M>(
        &mut self,
        hierarchy: &Hierarchy<E>,
        to_process: &mut Vec<NodeRef>,
        unsat_nodes: &mut HashSet<NodeRef>,
        built: &mut usize,
        total: usize,
        monitor: &mut M,
    ) -> bool
    where
        M: ClassificationProgressMonitor<E> + ?Sized,
    {
        // The pool borrows the oracle exclusively for its lifetime, so move the
        // oracle OUT of `self` for the duration of the pipeline. The harvest below
        // never touches the oracle (only the worklist + the known/possible graphs),
        // so `self` stays freely mutable; we restore the oracle before returning.
        let mut oracle = self.oracle.take().expect("oracle present");

        // Run the entire pipeline inside a block so the pool's exclusive borrow of
        // `oracle` ends (and the workers are joined) before we move `oracle` back
        // into `self`. The block evaluates to whether a streaming pool was used.
        let used_streaming = {
            let pool = oracle.streaming_pool();
            if pool.is_none() {
                // No streaming backend: drop the (empty) borrow, restore the oracle,
                // and fall back to the batched-round path.
                drop(pool);
                self.oracle = Some(oracle);
                return false;
            }
            let mut pool = pool.unwrap();

        // The in-flight set maps each dispatched concept back to its hierarchy node
        // (needed for descendant unsat-propagation), so `recv` (which returns only
        // the concept) can recover the node. A concept is dispatched at most once at
        // a time, so the key is unique among in-flight builds.
        let mut in_flight: HashMap<E, NodeRef> = HashMap::new();
        let worker_budget = pool.worker_count().max(1);
        // Memory governor: the worklist's full width keeps every worker saturating
        // its own satisfiability tableau concurrently, which is the throughput win
        // for the (vast majority) cheap classes. A handful of pathological classes,
        // though, each transiently grow a worker tableau to multiple GB; `N` of
        // those at once OOM a small box. `governor` collapses the effective budget
        // to a single in-flight build while resident memory is high (and restores
        // full width once it falls back), so at most one giant tableau is live at a
        // time under pressure. See `MemoryGovernor`.
        let mut governor = MemoryGovernor::new(worker_budget);

        loop {
            // Keep the pipeline full: dispatch not-yet-processed concepts until the
            // (possibly memory-throttled) worker budget is saturated or the worklist
            // is exhausted.
            let budget = governor.budget();
            while in_flight.len() < budget {
                let node = match to_process.pop() {
                    Some(n) => n,
                    None => break,
                };
                let concept = hierarchy.node(node).representative().clone();
                if self.concept_has_been_processed_already(&concept) {
                    continue;
                }
                // A concept already in flight need not be dispatched again; a second
                // build would be redundant (harvest is idempotent) but wastes a
                // worker, so skip it.
                if in_flight.contains_key(&concept) {
                    continue;
                }
                in_flight.insert(concept.clone(), node);
                pool.dispatch(concept);
            }

            // Termination: nothing in flight and the worklist is drained.
            if in_flight.is_empty() {
                break;
            }

            // Block for exactly one completed result and harvest it immediately
            // (no reorder buffer -> RAM bounded by in-flight tableaux only).
            let (concept, model) = match pool.recv() {
                Some(r) => r,
                // Pool drained with builds still outstanding would be a bug; treat
                // as termination to avoid a hang (in_flight is non-empty here).
                None => break,
            };
            let node = match in_flight.remove(&concept) {
                Some(n) => n,
                // A result for a concept we did not dispatch (should not happen);
                // drop it.
                None => continue,
            };

            // A sibling completed earlier may have made this concept unsatisfiable
            // (and thus processed) since its build was dispatched; its read-off is
            // now stale. Drop it -- the same guard the serial loop applies.
            if self.concept_has_been_processed_already(&concept) {
                continue;
            }
            *built += 1;
            monitor.classification_progress(*built, total);
            self.harvest_leaf_node_result(
                hierarchy,
                node,
                &concept,
                model,
                to_process,
                unsat_nodes,
            );
        }

            // Drop the pool (closes the work channel + joins the workers, releasing
            // its exclusive borrow of `oracle`) at the end of this block.
            drop(pool);
            true
        };

        // Restore the oracle so the later possible-subsumer resolution phase (in
        // `classify_with_monitor`) can use it again.
        self.oracle = Some(oracle);
        used_streaming
    }

    /// `updatePossibleSubsumers`: for every concept appearing on a node of the
    /// model, harvest or prune its possible subsumers against that node's label.
    /// A concept seen for the first time (`possible` empty) takes the node's whole
    /// label (`readPossibleSubsumersFromNodeLabel`, mirrored to inverses in role
    /// mode via `add_possible_subsumption`); a concept already seen has its possible
    /// subsumers intersected with the label (`prunePossibleSubsumersOfConcept`,
    /// which removes directly and is *not* mirrored).
    fn update_possible_subsumers(&mut self, node_labels: &[HashSet<E>]) {
        for label in node_labels {
            let label: HashSet<E> =
                label.iter().filter(|c| self.elements.contains(c)).cloned().collect();
            for concept in &label {
                if self.possible_subsumptions.successors_is_empty(concept) {
                    for sup in &label {
                        self.add_possible_subsumption(concept, sup);
                    }
                } else {
                    let current = self.possible_subsumptions.get_successors(concept);
                    let to_remove: HashSet<E> =
                        current.into_iter().filter(|s| !label.contains(s)).collect();
                    self.possible_subsumptions.remove_successors(concept, &to_remove);
                }
            }
        }
    }

    /// `prunePossibleSubsumers`: for every concept appearing on a node of the model,
    /// remove from its possible subsumers any candidate not asserted on that node
    /// (`prunePossibleSubsumersOfConcept`). Unlike [`update_possible_subsumers`] this
    /// is prune-only -- it never *adds* a concept's whole node label as fresh
    /// possibles, matching HermiT's `doesSubsume`, which only narrows the already
    /// established possible-subsumer sets.
    fn prune_possible_subsumers(&mut self, node_labels: &[HashSet<E>]) {
        for label in node_labels {
            let label: HashSet<E> =
                label.iter().filter(|c| self.elements.contains(c)).cloned().collect();
            for concept in &label {
                if self.possible_subsumptions.successors_is_empty(concept) {
                    continue;
                }
                let current = self.possible_subsumptions.get_successors(concept);
                let to_remove: HashSet<E> =
                    current.into_iter().filter(|s| !label.contains(s)).collect();
                self.possible_subsumptions.remove_successors(concept, &to_remove);
            }
        }
    }

    /// `buildHierarchyOfUnknownPossible`: the small hierarchy over the unknown
    /// possible subsumers (plus top and bottom), ordered by known subsumption.
    fn build_hierarchy_of_unknown_possible(&self, unknown: &HashSet<E>) -> Hierarchy<E> {
        let mut small: Graph<E> = Graph::new();
        for u0 in unknown {
            small.add_edge(self.bottom_element.clone(), u0.clone());
            small.add_edge(u0.clone(), self.top_element.clone());
            let known = self.all_known_subsumers(u0);
            for u1 in unknown {
                if known.contains(u1) {
                    small.add_edge(u0.clone(), u1.clone());
                }
            }
        }
        let mut with_top_bottom = unknown.clone();
        with_top_bottom.insert(self.bottom_element.clone());
        with_top_bottom.insert(self.top_element.clone());
        self.build_transitively_reduced_hierarchy(&small, &with_top_bottom)
    }

    /// `checkUnknownSubsumersUsingEnhancedTraversal`: walk the small hierarchy top
    /// down, testing `does_subsume(child, picked)` and recording confirmed
    /// subsumptions (with the child node's equivalents).
    fn check_unknown_subsumers_using_enhanced_traversal(
        &mut self,
        hierarchy: &Hierarchy<E>,
        start_node: NodeRef,
        picked: &E,
    ) {
        let mut visited: HashSet<NodeRef> = HashSet::new();
        visited.insert(start_node);
        let mut to_process: VecDeque<NodeRef> = VecDeque::new();
        to_process.push_back(start_node);
        while let Some(current) = to_process.pop_front() {
            let children: Vec<NodeRef> =
                hierarchy.node(current).child_nodes().iter().copied().collect();
            for child in children {
                if visited.contains(&child) {
                    continue;
                }
                let element = hierarchy.node(child).representative().clone();
                // `Relation.doesSubsume` shortcuts (QuasiOrderClassification.classify):
                // an already-known subsumer needs no test, and an element that is not
                // even a possible subsumer of `picked` cannot subsume it.
                let subsumes = if self.all_known_subsumers(picked).contains(&element) {
                    true
                } else if !self.possible_subsumptions.successor_contains(picked, &element) {
                    false
                } else {
                    // `Relation.doesSubsume`: run the tableau test and harvest the
                    // model read-off it produces.
                    let (subsumed, read_off) =
                        self.oracle_mut().does_subsume_with_read_off(&element, picked);
                    if let Some(read_off) = read_off {
                        // Not subsumed: a witnessing model exists. Harvest `picked`'s
                        // deterministic subsumers (readKnownSubsumersFromRootNode) and
                        // prune every concept's possible subsumers against the model
                        // (prunePossibleSubsumers).
                        for sup in &read_off.query_known {
                            if self.elements.contains(sup) {
                                self.add_known_subsumption(picked, sup);
                            }
                        }
                        if let Some(node_labels) = read_off.node_labels {
                            self.prune_possible_subsumers(&node_labels);
                        }
                    }
                    // m_possibleSubsumptions.getSuccessors(picked)
                    //   .removeAll(getAllKnownSubsumers(picked)).
                    let known = self.all_known_subsumers(picked);
                    self.possible_subsumptions.remove_successors(picked, &known);
                    subsumed
                };
                if subsumes {
                    self.add_known_subsumption(picked, &element);
                    let equivalents = hierarchy.node(child).equivalent_elements().clone();
                    self.add_known_subsumptions(picked, &equivalents);
                    if visited.insert(child) {
                        to_process.push_back(child);
                    }
                }
                visited.insert(child);
            }
        }
    }

    /// `isEveryPossibleSubsumerNonSubsumer`: for a small possible-subsumer set
    /// (`lowerBound < size < upperBound`, i.e. 3..=6), a single batched test asks
    /// whether `picked` is subsumed by the union of the unknown possibles. If it
    /// is NOT, none of them subsume `picked`, so the enhanced traversal can be
    /// skipped (the caller clears the possibles afterwards regardless). If it IS,
    /// HermiT reads the deterministic known subsumers off the witnessing model
    /// (`readKnownSubsumersFromRootNode`) and removes the (transitively) known
    /// subsumers from `picked`'s possible set, an answer-neutral optimization that
    /// avoids redundant pairwise subsumption tests in the enhanced traversal. If
    /// the oracle cannot run the batched test, fall back to the traversal.
    fn is_every_possible_subsumer_non_subsumer(
        &mut self,
        unknown: &HashSet<E>,
        picked: &E,
    ) -> bool {
        // `isEveryPossibleSubsumerNonSubsumer(...,2,7)`: only worth a batched
        // satisfiability test for a possible-subsumer set whose size is in (2,7).
        if unknown.len() > 2 && unknown.len() < 7 {
            if let Some(result) = self.oracle_mut().is_subsumed_by_union(picked, unknown) {
                if result.subsumed {
                    // readKnownSubsumersFromRootNode(pickedElement, ...) then
                    // m_possibleSubsumptions.getSuccessors(pickedElement)
                    //   .removeAll(getAllKnownSubsumers(pickedElement)).
                    for sup in &result.query_known {
                        if self.elements.contains(sup) {
                            self.add_known_subsumption(picked, sup);
                        }
                    }
                    let known = self.all_known_subsumers(picked);
                    self.possible_subsumptions.remove_successors(picked, &known);
                }
                return !result.subsumed;
            }
        }
        false
    }

    /// `buildTransitivelyReducedHierarchy`: each element's subsumers are its known
    /// successors plus top and itself; bottom's subsumers are all elements. Then
    /// `DeterministicClassification.buildHierarchy` does the SCC + reduction.
    fn build_transitively_reduced_hierarchy(
        &self,
        known_subsumptions: &Graph<E>,
        elements: &HashSet<E>,
    ) -> Hierarchy<E> {
        self.build_transitively_reduced_hierarchy_with_monitor(
            known_subsumptions,
            elements,
            &mut NoProgressMonitor,
        )
    }

    /// As [`build_transitively_reduced_hierarchy`](Self::build_transitively_reduced_hierarchy),
    /// but fires `monitor` once per element of the subsumer graph (via
    /// `build_hierarchy_with_monitor`). The intermediate hierarchy builds call the
    /// `NoProgressMonitor` variant; only the final result build (in
    /// [`classify_with_monitor`](Self::classify_with_monitor)) passes a real
    /// monitor, so each classified element is reported exactly once.
    fn build_transitively_reduced_hierarchy_with_monitor<M>(
        &self,
        known_subsumptions: &Graph<E>,
        elements: &HashSet<E>,
        monitor: &mut M,
    ) -> Hierarchy<E>
    where
        M: ClassificationProgressMonitor<E> + ?Sized,
    {
        use std::collections::HashMap;
        let mut subsumers: HashMap<E, HashSet<E>> = HashMap::new();
        for element in elements {
            let mut extended = known_subsumptions.get_successors(element);
            extended.insert(self.top_element.clone());
            extended.insert(element.clone());
            subsumers.insert(element.clone(), extended);
        }
        subsumers.insert(self.bottom_element.clone(), elements.clone());
        build_hierarchy_with_monitor(
            self.top_element.clone(),
            self.bottom_element.clone(),
            subsumers,
            monitor,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    /// An in-memory oracle backed by a ground-truth subsumption table:
    /// `truth[x]` is the set of concepts that subsume `x` (reflexive, including
    /// top). `unsat` lists unsatisfiable concepts. `build_model` returns no
    /// deterministic known subsumers (so everything is a *possible* subsumer to be
    /// confirmed by `does_subsume`), exercising the possible-resolution path.
    struct TruthOracle {
        truth: HashMap<&'static str, HashSet<&'static str>>,
        unsat: HashSet<&'static str>,
    }
    impl SubsumptionOracle<&'static str> for TruthOracle {
        fn build_model(&mut self, concept: &&'static str) -> Option<ModelReadOff<&'static str>> {
            if self.unsat.contains(concept) {
                return None;
            }
            // Possible subsumers: every concept's label includes its true
            // subsumers; expose them as "possible" (no deterministic knowns, no
            // cross-concept harvesting).
            let possible: HashSet<&'static str> =
                self.truth.get(concept).cloned().unwrap_or_default();
            Some(ModelReadOff {
                query_known: HashSet::new(),
                query_possible: possible,
                node_labels: None,
            })
        }
        fn does_subsume(&mut self, parent: &&'static str, child: &&'static str) -> bool {
            self.truth.get(child).map_or(false, |s| s.contains(parent))
        }
        fn is_subsumed_by_union(
            &mut self,
            child: &&'static str,
            candidates: &HashSet<&'static str>,
        ) -> Option<UnionTestResult<&'static str>> {
            // In the single ground-truth model, `child` is subsumed by the union
            // iff at least one candidate actually subsumes it. This oracle exposes
            // no deterministic known subsumers off the witnessing model.
            let subsumers = self.truth.get(child).cloned().unwrap_or_default();
            Some(UnionTestResult {
                subsumed: candidates.iter().any(|c| subsumers.contains(c)),
                query_known: HashSet::new(),
            })
        }
    }

    // The batched test returns "all non-subsumers" exactly when `picked` is not
    // subsumed by the union of the unknown possibles (3..=6 of them, top excluded).
    #[test]
    fn batched_non_subsumer_test() {
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("A", ["A", "B", "top"].into_iter().collect());
        let oracle = TruthOracle { truth, unsat: HashSet::new() };
        let elements: HashSet<&str> =
            ["top", "A", "B", "C", "D", "E", "bottom"].into_iter().collect();
        let mut classifier = QuasiOrderClassification::new(oracle, "top", "bottom", elements);
        // None of C, D, E subsume A -> every possible subsumer is a non-subsumer.
        let none: HashSet<&str> = ["C", "D", "E"].into_iter().collect();
        assert!(classifier.is_every_possible_subsumer_non_subsumer(&none, &"A"));
        // B subsumes A -> not every possible is a non-subsumer.
        let some: HashSet<&str> = ["B", "C", "D"].into_iter().collect();
        assert!(!classifier.is_every_possible_subsumer_non_subsumer(&some, &"A"));
        // Outside the (2,7) size window, the batched test is not used.
        let pair: HashSet<&str> = ["C", "D"].into_iter().collect();
        assert!(!classifier.is_every_possible_subsumer_non_subsumer(&pair, &"A"));
        // top among the unknowns -> skip the batched test (top trivially subsumes).
        let with_top: HashSet<&str> = ["top", "C", "D"].into_iter().collect();
        assert!(!classifier.is_every_possible_subsumer_non_subsumer(&with_top, &"A"));
    }

    #[test]
    fn classifies_a_chain_via_possible_resolution() {
        // A ⊑ B ⊑ C, all satisfiable. truth[x] = subsumers of x (incl. top, self).
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("top", ["top"].into_iter().collect());
        truth.insert("C", ["C", "top"].into_iter().collect());
        truth.insert("B", ["B", "C", "top"].into_iter().collect());
        truth.insert("A", ["A", "B", "C", "top"].into_iter().collect());
        truth.insert("bottom", ["bottom", "A", "B", "C", "top"].into_iter().collect());

        let oracle = TruthOracle { truth, unsat: HashSet::new() };
        let elements: HashSet<&str> = ["top", "A", "B", "C", "bottom"].into_iter().collect();
        let classifier = QuasiOrderClassification::new(oracle, "top", "bottom", elements);
        let hierarchy = classifier.classify();

        let a = hierarchy.node_for_element(&"A").unwrap();
        let b = hierarchy.node_for_element(&"B").unwrap();
        let c = hierarchy.node_for_element(&"C").unwrap();
        // A < B < C in the ancestor relation.
        assert!(hierarchy.ancestor_nodes(a).contains(&b));
        assert!(hierarchy.ancestor_nodes(b).contains(&c));
        assert!(hierarchy.ancestor_nodes(a).contains(&c));
        // Transitive reduction: B is a direct child of C, A is not.
        assert!(hierarchy.node(c).child_nodes().contains(&b));
        assert!(!hierarchy.node(c).child_nodes().contains(&a));
    }

    #[test]
    fn unsatisfiable_concept_goes_to_bottom() {
        // A ⊑ B, but A is unsatisfiable -> A collapses into the bottom node.
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("top", ["top"].into_iter().collect());
        truth.insert("B", ["B", "top"].into_iter().collect());
        truth.insert("A", ["A", "B", "top"].into_iter().collect());
        truth.insert("bottom", ["bottom", "A", "B", "top"].into_iter().collect());

        let oracle = TruthOracle {
            truth,
            unsat: ["A"].into_iter().collect(),
        };
        let elements: HashSet<&str> = ["top", "A", "B", "bottom"].into_iter().collect();
        let classifier = QuasiOrderClassification::new(oracle, "top", "bottom", elements);
        let hierarchy = classifier.classify();

        assert_eq!(
            hierarchy.node_for_element(&"A").unwrap(),
            hierarchy.bottom_node()
        );
    }

    #[test]
    fn role_mode_mirrors_subsumptions_to_inverses() {
        // Roles r ⊑ s with inverses r⁻, s⁻. Concepts: r, s, ri (=r⁻), si (=s⁻).
        // A told inclusion r ⊑ s must also yield r⁻ ⊑ s⁻ via the inverse mirror.
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("top", ["top"].into_iter().collect());
        truth.insert("s", ["s", "top"].into_iter().collect());
        truth.insert("si", ["si", "top"].into_iter().collect());
        truth.insert("r", ["r", "s", "top"].into_iter().collect());
        truth.insert("ri", ["ri", "si", "top"].into_iter().collect());
        truth.insert("bottom", ["bottom", "r", "s", "ri", "si", "top"].into_iter().collect());
        let oracle = TruthOracle { truth, unsat: HashSet::new() };

        let mut inverse: HashMap<&str, &str> = HashMap::new();
        inverse.insert("r", "ri");
        inverse.insert("ri", "r");
        inverse.insert("s", "si");
        inverse.insert("si", "s");

        let elements: HashSet<&str> =
            ["top", "r", "s", "ri", "si", "bottom"].into_iter().collect();
        let mut classifier = QuasiOrderClassification::new_for_roles(
            oracle,
            "top",
            "bottom",
            elements,
            Some(inverse),
        );
        // Told: r ⊑ s (same arguments). The mirror should add r⁻ ⊑ s⁻ as well.
        classifier.initialise_known_subsumptions_for_roles(&[("r", "s", false)]);
        let hierarchy = classifier.classify();

        let r = hierarchy.node_for_element(&"r").unwrap();
        let s = hierarchy.node_for_element(&"s").unwrap();
        let ri = hierarchy.node_for_element(&"ri").unwrap();
        let si = hierarchy.node_for_element(&"si").unwrap();
        assert!(hierarchy.ancestor_nodes(r).contains(&s), "r ⊑ s");
        assert!(hierarchy.ancestor_nodes(ri).contains(&si), "r⁻ ⊑ s⁻ (mirrored)");
    }

    #[test]
    fn equivalent_concepts_share_a_node() {
        // P ≡ Q (each subsumes the other), unrelated to the rest.
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("top", ["top"].into_iter().collect());
        truth.insert("P", ["P", "Q", "top"].into_iter().collect());
        truth.insert("Q", ["Q", "P", "top"].into_iter().collect());
        truth.insert("bottom", ["bottom", "P", "Q", "top"].into_iter().collect());

        let oracle = TruthOracle { truth, unsat: HashSet::new() };
        let elements: HashSet<&str> = ["top", "P", "Q", "bottom"].into_iter().collect();
        let classifier = QuasiOrderClassification::new(oracle, "top", "bottom", elements);
        let hierarchy = classifier.classify();

        assert_eq!(
            hierarchy.node_for_element(&"P").unwrap(),
            hierarchy.node_for_element(&"Q").unwrap()
        );
    }
}
