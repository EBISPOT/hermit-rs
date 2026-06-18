// Port of org.semanticweb.HermiT.tableau.Tableau (node-management subset).
//
// The `Tableau` owns the node arena and coordinates the expansion. HermiT's
// many managers (extension tables, hyperresolution, merging, existential
// expansion, clash, datatypes, ...) hold a back-reference to the `Tableau` and
// mutate shared state; in Rust they become `impl` blocks / fields on this one
// owning struct.
//
// This file ports the node lifecycle (allocation with a free list, the tableau
// node linked list, merge / prune / backtrack, and the canonical-node traversals
// from `Node`). The `ExistentialExpansionStrategy` node-lifecycle callbacks
// (nodeInitialized, nodeStatusChanged, nodesMerged, nodeDestroyed) that Java
// forwards to the strategy object are not forwarded here; the reasoning-relevant
// subset of that interface is handled directly by the `Tableau`.
#![allow(dead_code)]

use crate::tableau::dependency_set::{DependencySet, DependencySetFactory, PermanentDependencySet};
use crate::tableau::extension_table::{
    new_binary_extension_table, new_ternary_extension_table, ExtensionTable,
};
use crate::tableau::node::{Node, NodeId, NodeState};
use crate::tableau::node_type::NodeType;

pub struct Tableau {
    pub(crate) dependency_set_factory: DependencySetFactory,

    // Node arena and the structural links HermiT keeps as object pointers.
    pub(crate) nodes: Vec<Node>,
    pub(crate) first_free_node: Option<NodeId>,
    pub(crate) first_tableau_node: Option<NodeId>,
    pub(crate) last_tableau_node: Option<NodeId>,
    pub(crate) last_merged_or_pruned_node: Option<NodeId>,

    pub(crate) allocated_nodes: i32,
    pub(crate) number_of_nodes_in_tableau: i32,
    pub(crate) number_of_merged_or_pruned_nodes: i32,
    pub(crate) number_of_node_creations: i32,

    // Extension tables (the ExtensionManager state).
    pub(crate) binary_extension_table: ExtensionTable,
    pub(crate) ternary_extension_table: ExtensionTable,
    pub(crate) clash_dependency_set: Option<PermanentDependencySet>,
    pub(crate) add_active: bool,
    pub(crate) needs_thing_extension: bool,
    pub(crate) needs_named_extension: bool,
    pub(crate) needs_rdfs_literal_extension: bool,
    /// Port of Tableau.m_checkDatatypes (Tableau.java:246,254):
    /// set once from permanentDLOntology.hasDatatypes() and used to skip
    /// the per-iteration checkDatatypeConstraints() scan for datatype-free ontologies.
    pub(crate) check_datatypes: bool,
    /// Whether a data node (`RootConstant`/`Concrete`) was created or had an
    /// assertion added since the last datatype check. HermiT's
    /// `DatatypeManager.checkDatatypeConstraints` drives off the DELTA_OLD
    /// retrievals, so it does no work in a round with no new data-range /
    /// inequality assertion. Mirror that: when no data-node change has occurred,
    /// the previous (clash-free) datatype check still holds, so the full rescan is
    /// skipped. Starts `true` so the first check always runs.
    pub(crate) datatype_check_needed: bool,
    /// Port of Tableau.m_checkUnknownDatatypeRestrictions (Tableau.java:247,255):
    /// set once from permanentDLOntology.hasUnknownDatatypeRestrictions() and used
    /// to gate the per-iteration applyUnknownDatatypeRestrictionSemantics() phase.
    /// This is only ever set (a non-empty unknown set is only produced) in the
    /// NON-default `ignoreUnsupportedDatatypes` mode, so the default path is
    /// untouched.
    pub(crate) check_unknown_datatype_restrictions: bool,
    /// Port of DatatypeManager.m_unknownDatatypeRestrictionsPermanent
    /// (DatatypeManager.java:52,81): the datatype restrictions over unsupported
    /// datatypes that `ignoreUnsupportedDatatypes` treats as fresh infinite value
    /// spaces (a restriction D and its negation ¬D must be kept disjoint).
    pub(crate) unknown_datatype_restrictions:
        std::collections::HashSet<crate::model::DatatypeRestriction>,

    // Branching / backtracking and ground disjunctions.
    pub(crate) branching_points: Vec<crate::tableau::branching::BranchingPointData>,
    pub(crate) current_branching_point: i32,
    pub(crate) nonbacktrackable_branching_point: i32,
    pub(crate) ground_disjunctions: Vec<Option<crate::tableau::branching::GroundDisjunctionData>>,
    pub(crate) first_ground_disjunction: Option<usize>,
    pub(crate) first_unprocessed_ground_disjunction: Option<usize>,
    pub(crate) ground_disjunction_header_manager:
        crate::tableau::hyperresolution::GroundDisjunctionHeaderManager,
    pub(crate) expanded_existentials: Vec<(crate::model::ExistentialConcept, NodeId)>,
    pub(crate) expanded_existentials_by_branching_point: Vec<usize>,

    /// Canonical NI root nodes for the nominal-introduction rule, keyed by
    /// `(owning root node, annotated equality, slot number)` -- the port of
    /// `NominalIntroductionManager.getNIRootFor`'s dedup index
    /// (`m_newRootNodesTable`/`m_newRootNodesIndex`). As in Java a cached entry is
    /// returned unconditionally (even when merged away); the caller canonicalizes.
    ///
    /// This index is part of the *backtracked* state: Java's
    /// `NominalIntroductionManager.backtrack` truncates `m_newRootNodesTable` to a
    /// per-branching-point watermark, destroying NI roots created after that point.
    /// `ni_roots_log` records insertion order and `ni_roots_by_branching_point`
    /// the per-level watermark so `backtrack_to` can drop the same entries; without
    /// this a recurring NI key would resolve to a destroyed/reused node id.
    pub(crate) ni_roots: rustc_hash::FxHashMap<
        (NodeId, crate::model::AnnotatedEquality, i32),
        NodeId,
    >,
    pub(crate) ni_roots_log: Vec<(NodeId, crate::model::AnnotatedEquality, i32)>,
    pub(crate) ni_roots_by_branching_point: Vec<usize>,

    /// `NominalIntroductionManager.m_annotatedEqualities`: the buffer of derived
    /// `AnnotatedEquality` facts whose cardinality is `> 1`. Java does NOT apply
    /// the nominal-introduction rule for these eagerly during hyperresolution;
    /// it buffers them here and drains the queue in `process_annotated_equalities`
    /// (called at the top of `do_iteration` and after each propagate-loop body),
    /// so the nondeterministic NI branching runs only after the deterministic
    /// hyperresolution/datatype saturation of the round. The buffer and its read
    /// cursor are backtracked state (Java `NominalIntroductionManager.backtrack`):
    /// `annotated_equalities_by_branching_point` / `first_unprocessed_ae_by_
    /// branching_point` record the per-level watermarks. (Cardinality `== 1` and
    /// the `canForgetAnnotation` cases are still applied eagerly, matching Java.)
    pub(crate) annotated_equalities: Vec<crate::tableau::branching::BufferedAnnotatedEquality>,
    pub(crate) first_unprocessed_annotated_equality: usize,
    pub(crate) annotated_equalities_by_branching_point: Vec<usize>,
    pub(crate) first_unprocessed_ae_by_branching_point: Vec<usize>,

    /// The validated-blocking validator, enabled (by the reasoner) only when the
    /// ontology has inverse roles, where plain pairwise blocking can be
    /// incomplete. `None` leaves `compute_blocking` as the pairwise pass.
    pub(crate) blocking_validator:
        Option<crate::tableau::blocking_validator::BlockingValidator>,

    /// The selected blocking strategy and direct-blocking checker, port of
    /// `Reasoner.createTableau`'s `blockingStrategy`/`directBlockingChecker`
    /// switch. The default (`Anywhere` + `Pairwise`) is HermiT's
    /// `OPTIMAL`/`OPTIMAL` choice for an ontology with inverse roles and matches
    /// the engine's historical hard-wired path; `configure_blocking` re-selects
    /// it from a `Configuration` + the ontology's expressivity flags.
    pub(crate) blocking_strategy_kind: crate::tableau::blocking_strategy::BlockingStrategyKind,
    pub(crate) direct_blocking_kind: crate::tableau::blocking_strategy::DirectBlockingKind,

    /// Whether the ontology has inverse roles. The validated direct-blocking
    /// checkers (`ValidatedSingleDirectBlockingChecker` /
    /// `ValidatedPairwiseDirectBlockingChecker`) gate node eligibility on
    /// `!hasInverses || parent is a tree/graph node`; set by `configure_blocking`.
    pub(crate) blocking_has_inverses: bool,

    /// The optional blocking-signature cache, port of `BlockingSignatureCache`.
    /// Present iff the configuration selects `CACHED` and the ontology has no
    /// nominals and the strategy is not a core/validated one (exactly
    /// `Reasoner.createTableau`'s guard). Populated from a found model by
    /// `cache_model_signatures` and consulted in `compute_blocking_*`.
    pub(crate) blocking_signature_cache:
        Option<crate::blocking::BlockingSignatureCache>,

    /// Incremental anywhere-blocking state (`AnywhereBlocking.m_firstChangedNode`
    /// + `m_currentBlockersCache`). `first_changed_node` is the lowest-`node_id`
    /// node whose blocking signature may have changed since the last
    /// `compute_blocking_anywhere`; `None` means nothing changed (so blocking is
    /// left untouched). The two maps are the persistent blockers cache, kept
    /// across calls: `blockers_cache_by_signature` maps a signature to its
    /// representative (lowest-id unblocked) node, and `blockers_cache_node_signature`
    /// is the reverse map used to remove a node by identity.
    pub(crate) first_changed_node: Option<NodeId>,
    /// `AnywhereValidatedBlocking.m_lastValidatedUnchangedNode`: the lowest-`node_id`
    /// node at or after which validation must resume (rewound by
    /// `validationInfoChanged`). `None` means "validate from the first node".
    pub(crate) last_validated_unchanged_node: Option<NodeId>,
    pub(crate) blockers_cache_by_signature:
        rustc_hash::FxHashMap<crate::blocking::CachedSignature, NodeId>,
    pub(crate) blockers_cache_node_signature:
        rustc_hash::FxHashMap<NodeId, crate::blocking::CachedSignature>,
    /// The validated strategy's persistent `ValidatedBlockersCache` (keyed by the
    /// core-label signature). Unlike the anywhere cache it keeps *all* candidate
    /// blockers per signature (`getPossibleBlockers`), since validation tries each
    /// in turn. The reverse map removes a node by identity.
    pub(crate) validated_blockers_by_signature: rustc_hash::FxHashMap<
        crate::tableau::blocking_strategy::ValidatedSignature,
        Vec<NodeId>,
    >,
    pub(crate) validated_blockers_node_signature: rustc_hash::FxHashMap<
        NodeId,
        crate::tableau::blocking_strategy::ValidatedSignature,
    >,

    /// Port of `Tableau.m_useDisjunctionLearning` (default `true`): gates the
    /// per-disjunct backtracking-count bookkeeping in `start_next_choice`.
    /// Answer-neutral -- only affects disjunct ordering.
    pub(crate) use_disjunction_learning: bool,

    /// Port of `Tableau.m_interruptFlag`. Built from
    /// `Configuration.individual_task_timeout` (default `-1` = no timeout = no
    /// behavioural change). `start_task`/`end_task` bracket the runCalculus loop
    /// and `check_interrupt()` is polled at the head of `do_iteration` and inside
    /// existential expansion.
    pub(crate) interrupt_flag: crate::tableau::interrupt_flag::InterruptFlag,

    /// Port of `Tableau.m_tableauMonitor`. `None` is a no-op at every hook site
    /// (matching Java's `if(m_tableauMonitor!=null)`); never changes an answer.
    pub(crate) monitor: Option<Box<dyn crate::monitor::TableauMonitor>>,

    /// Sticky record of the interrupt that fired during the current task.
    /// Java's `checkInterrupt()` throws immediately; the engine's `&mut self`
    /// methods that cannot return a `Result` (e.g. `expand_existentials`) instead
    /// latch the error here so the public `is_consistent` loop can surface it as
    /// an `Err`. Never set with the default `-1` timeout and no explicit
    /// interrupt, so there is zero behavioural change.
    pub(crate) pending_interrupt:
        Option<crate::tableau::interrupt_flag::InterruptError>,

    /// The configured existential-expansion strategy. Port of HermiT's
    /// `m_existentialExpansionStrategy` choice (`Reasoner.createTableau`'s switch
    /// on `Configuration.existentialStrategyType`). `CreationOrder` (the default)
    /// is realized directly by `expand_existentials`; `IndividualReuse`/`El`
    /// select the [`IndividualReuseStrategy`](crate::existentials::IndividualReuseStrategy)
    /// bookkeeping below. This is `CreationOrder` by default, so the default path
    /// is byte-for-byte unchanged.
    pub(crate) existential_strategy_type:
        crate::configuration::ExistentialStrategyType,

    /// The individual-reuse strategy object, present iff
    /// `existential_strategy_type` selects reuse. Holds the reuse map and the
    /// always/never-reuse concept sets (`IndividualReuseStrategy`'s bookkeeping),
    /// so the config is honoured and `model_found` runs; see
    /// `expand_existentials` for the dispatch.
    pub(crate) individual_reuse_strategy:
        Option<crate::existentials::IndividualReuseStrategy>,

    /// The functional-role map, port of
    /// `ExistentialExpansionManager.m_functionalRoles`. Maps each role `r` that
    /// is a sub-role of some functional super-role to the set of "relevant
    /// roles" -- the sub-roles of that functional super-role -- whose successors
    /// are candidates for the single functional successor of `r`. Populated once
    /// from the permanent DL clauses by `set_functional_roles_from_clauses`
    /// (mirroring `updateFunctionalRoles`/`loadDLClausesIntoGraph`). Empty by
    /// default, so without population every role is treated as non-functional and
    /// existential expansion is byte-for-byte the old normal-expansion behaviour.
    pub(crate) functional_roles:
        rustc_hash::FxHashMap<crate::model::Role, Vec<crate::model::Role>>,

    /// The description-graph manager, port of `Tableau.m_descriptionGraphManager`.
    /// Built (empty) by the constructor and populated by `set_description_graphs`
    /// from the ontology's description graphs (`Reasoner.createTableau` ->
    /// `new DescriptionGraphManager(this)`, which reads
    /// `m_permanentDLOntology.getAllDescriptionGraphs()`). Empty by default, so
    /// every hook (`initialize_node`/`destroy_node`, `check_graph_constraints`,
    /// `merge_graphs`, the `ExistsDescriptionGraph` expansion) is a no-op and an
    /// ontology without description graphs behaves exactly as before.
    pub(crate) description_graph_manager:
        crate::tableau::description_graph_manager::DescriptionGraphManager,
}

impl Tableau {
    /// Builds a tableau with HermiT's default configuration (no timeout, no
    /// monitor, disjunction-learning on).
    pub fn new() -> Tableau {
        Tableau::with_configuration(&crate::configuration::Configuration::default())
    }

    /// Port of the `Tableau` constructor's configuration-dependent wiring.
    /// Reads `use_disjunction_learning`, `individual_task_timeout`, and
    /// `tableau_monitor_type` off the configuration.
    pub fn with_configuration(
        configuration: &crate::configuration::Configuration,
    ) -> Tableau {
        let mut tableau = Tableau::with_fields(
            configuration.use_disjunction_learning,
            crate::tableau::interrupt_flag::InterruptFlag::new(
                configuration.individual_task_timeout,
            ),
        );
        tableau.monitor = default_monitor_for(configuration.tableau_monitor_type);
        // Honour the configured existential-expansion strategy.
        tableau.set_existential_strategy(
            configuration.existential_strategy_type,
            &configuration.parameters,
        );
        tableau
    }

    /// Selects the existential-expansion strategy from the configuration,
    /// mirroring `Reasoner.createTableau`'s switch on
    /// `Configuration.existentialStrategyType`:
    ///   * `CREATION_ORDER` -> `CreationOrderStrategy` (the default; no reuse).
    ///   * `EL`             -> `IndividualReuseStrategy(_, isDeterministic=true)`.
    ///   * `INDIVIDUAL_REUSE` -> `IndividualReuseStrategy(_, isDeterministic=false)`.
    ///
    /// For reuse strategies the always/never-reuse concept sets are read from the
    /// `IndividualReuseStrategy.reuseAlways` / `.reuseNever` parameters (HermiT's
    /// `IndividualReuseStrategy.initialize`).
    pub(crate) fn set_existential_strategy(
        &mut self,
        strategy_type: crate::configuration::ExistentialStrategyType,
        parameters: &std::collections::HashMap<String, String>,
    ) {
        use crate::configuration::ExistentialStrategyType;
        self.existential_strategy_type = strategy_type;
        self.individual_reuse_strategy = match strategy_type {
            ExistentialStrategyType::CreationOrder => None,
            ExistentialStrategyType::El => Some(
                crate::existentials::IndividualReuseStrategy::from_parameters(true, parameters),
            ),
            ExistentialStrategyType::IndividualReuse => Some(
                crate::existentials::IndividualReuseStrategy::from_parameters(false, parameters),
            ),
        };
    }

    /// Port of `runCalculus`'s `m_existentialExpansionStrategy.modelFound()` call
    /// on a clash-free saturation. For the reuse strategy this records that
    /// concepts not reused this run are never reused again. A no-op for the
    /// default creation-order strategy.
    pub(crate) fn existential_strategy_model_found(&mut self) {
        if let Some(strategy) = self.individual_reuse_strategy.as_mut() {
            strategy.model_found();
        }
    }

    /// Wires a reasoner-wide shared never-reuse set into this tableau's reuse
    /// strategy, so the `IndividualReuseStrategy`'s `m_dontReuseConceptsEver`
    /// learning persists across the per-test tableaux (HermiT keeps one tableau
    /// for the reasoner's lifetime; this port builds one per test, so the learned
    /// set is shared instead). A no-op for the default creation-order strategy.
    pub(crate) fn adopt_shared_reuse_never(
        &mut self,
        shared: crate::existentials::SharedDontReuseEver,
    ) {
        if let Some(strategy) = self.individual_reuse_strategy.as_mut() {
            strategy.adopt_shared_dont_reuse_ever(shared);
        }
    }

    fn with_fields(
        use_disjunction_learning: bool,
        interrupt_flag: crate::tableau::interrupt_flag::InterruptFlag,
    ) -> Tableau {
        // `needs_dependency_sets` is true unless the ontology is Horn and the
        // expansion strategy is deterministic; defaulting to true is sound.
        let needs_dependency_sets = true;
        Tableau {
            dependency_set_factory: DependencySetFactory::new(),
            nodes: Vec::new(),
            first_free_node: None,
            first_tableau_node: None,
            last_tableau_node: None,
            last_merged_or_pruned_node: None,
            allocated_nodes: 0,
            number_of_nodes_in_tableau: 0,
            number_of_merged_or_pruned_nodes: 0,
            number_of_node_creations: 0,
            binary_extension_table: new_binary_extension_table(needs_dependency_sets),
            ternary_extension_table: new_ternary_extension_table(needs_dependency_sets),
            clash_dependency_set: None,
            add_active: false,
            needs_thing_extension: false,
            needs_named_extension: false,
            needs_rdfs_literal_extension: false,
            check_datatypes: false,
            datatype_check_needed: true,
            check_unknown_datatype_restrictions: false,
            unknown_datatype_restrictions: std::collections::HashSet::new(),
            branching_points: Vec::new(),
            current_branching_point: -1,
            nonbacktrackable_branching_point: -1,
            ground_disjunctions: Vec::new(),
            first_ground_disjunction: None,
            first_unprocessed_ground_disjunction: None,
            ground_disjunction_header_manager:
                crate::tableau::hyperresolution::GroundDisjunctionHeaderManager::new(),
            expanded_existentials: Vec::new(),
            expanded_existentials_by_branching_point: Vec::new(),
            first_changed_node: None,
            last_validated_unchanged_node: None,
            validated_blockers_by_signature: rustc_hash::FxHashMap::default(),
            validated_blockers_node_signature: rustc_hash::FxHashMap::default(),
            blockers_cache_by_signature: rustc_hash::FxHashMap::default(),
            blockers_cache_node_signature: rustc_hash::FxHashMap::default(),
            ni_roots: rustc_hash::FxHashMap::default(),
            ni_roots_log: Vec::new(),
            ni_roots_by_branching_point: Vec::new(),
            annotated_equalities: Vec::new(),
            first_unprocessed_annotated_equality: 0,
            annotated_equalities_by_branching_point: Vec::new(),
            first_unprocessed_ae_by_branching_point: Vec::new(),
            blocking_validator: None,
            blocking_strategy_kind:
                crate::tableau::blocking_strategy::BlockingStrategyKind::Anywhere,
            direct_blocking_kind:
                crate::tableau::blocking_strategy::DirectBlockingKind::Pairwise,
            blocking_has_inverses: false,
            blocking_signature_cache: None,
            use_disjunction_learning,
            interrupt_flag,
            monitor: None,
            pending_interrupt: None,
            existential_strategy_type:
                crate::configuration::ExistentialStrategyType::CreationOrder,
            individual_reuse_strategy: None,
            functional_roles: rustc_hash::FxHashMap::default(),
            description_graph_manager:
                crate::tableau::description_graph_manager::DescriptionGraphManager::default(),
        }
    }

    /// Install the ontology's description graphs, port of `Reasoner.createTableau`
    /// constructing `new DescriptionGraphManager(this)` from
    /// `m_permanentDLOntology.getAllDescriptionGraphs()`. Call once after
    /// constructing the tableau and before reasoning; the reasoner threads the
    /// `DLOntology`'s graphs here. An empty slice leaves the manager a no-op.
    pub fn set_description_graphs(
        &mut self,
        graphs: &[crate::model::DescriptionGraph],
    ) {
        // The per-graph extension tables carry dependency sets exactly when the
        // binary/ternary tables do (`!isDeterministic()`); this port keeps that
        // flag at `true`, matching `new_binary_extension_table` above.
        self.description_graph_manager =
            crate::tableau::description_graph_manager::DescriptionGraphManager::new(graphs, true);
    }

    /// Attaches a tableau monitor. `None` (the default) makes every hook a
    /// no-op, matching Java's `if(m_tableauMonitor!=null)` guards.
    pub fn set_monitor(&mut self, monitor: Option<Box<dyn crate::monitor::TableauMonitor>>) {
        self.monitor = monitor;
    }

    /// Detaches and returns the attached monitor, so callers can read off
    /// the accumulated statistics.
    pub fn take_monitor(&mut self) -> Option<Box<dyn crate::monitor::TableauMonitor>> {
        self.monitor.take()
    }

    /// A handle that can interrupt this tableau's current task from another
    /// thread.
    pub fn interrupt_handle(&self) -> crate::tableau::interrupt_flag::InterruptHandle {
        self.interrupt_flag.interrupt_handle()
    }

    /// Polls the interrupt flag. `Err` only when an interrupt actually fired
    /// (never with the default `-1` timeout and no explicit interrupt).
    pub fn check_interrupt(
        &self,
    ) -> Result<(), crate::tableau::interrupt_flag::InterruptError> {
        self.interrupt_flag.check_interrupt()
    }

    /// Brackets the start of a reasoning task: resets the interrupt flag and
    /// starts the timeout clock. Mirrors `m_interruptFlag.startTask()` in
    /// `Tableau.runCalculus`.
    pub fn start_task(&mut self) {
        self.pending_interrupt = None;
        self.interrupt_flag.start_task();
    }

    /// Latches an interrupt at a hook site that cannot return a `Result`.
    /// With the default `-1` timeout and no explicit interrupt this is a no-op,
    /// so there is zero behavioural change.
    #[inline]
    pub(crate) fn note_interrupt(&mut self) {
        if self.pending_interrupt.is_none() {
            if let Err(error) = self.interrupt_flag.check_interrupt() {
                self.pending_interrupt = Some(error);
            }
        }
    }

    /// The interrupt that fired during the current task, if any.
    pub fn take_pending_interrupt(
        &mut self,
    ) -> Option<crate::tableau::interrupt_flag::InterruptError> {
        self.pending_interrupt.take()
    }

    /// Brackets the end of a reasoning task.
    pub fn end_task(&mut self) {
        self.interrupt_flag.end_task();
    }

    /// Emits a monitor event if a monitor is attached (the `if(m_tableauMonitor
    /// !=null)` guard). No-op otherwise.
    #[inline]
    pub(crate) fn monitor_event(&mut self, f: impl FnOnce(&mut dyn crate::monitor::TableauMonitor)) {
        if let Some(monitor) = self.monitor.as_deref_mut() {
            f(monitor);
        }
    }

    /// Enables validated blocking with the given validator (built from the DL
    /// clauses). Called by the reasoner for ontologies with inverse roles.
    pub fn set_blocking_validator(
        &mut self,
        validator: crate::tableau::blocking_validator::BlockingValidator,
    ) {
        self.blocking_validator = Some(validator);
    }

    /// Port of `Reasoner.createTableau`'s blocking-construction decision tree.
    /// Selects the direct-blocking checker, the blocking strategy, and the
    /// optional signature cache from `configuration` and the ontology's
    /// expressivity flags (`has_inverse_roles`/`has_nominals`), exactly mirroring
    /// the Java switch (Reasoner.java ~1967-2024):
    ///
    /// * `DirectBlockingType`:
    ///   - `OPTIMAL`  -> core-validated => single (validated); else pairwise iff
    ///     `has_inverse_roles`, else single.
    ///   - `SINGLE`   -> single (validated when core).
    ///   - `PAIR_WISE`-> pairwise (validated when core).
    /// * `BlockingStrategyType`:
    ///   - `ANCESTOR`            -> ancestor blocking.
    ///   - `ANYWHERE`/`OPTIMAL`  -> anywhere blocking.
    ///   - `SIMPLE_CORE`/`COMPLEX_CORE` -> anywhere *validated* blocking (the
    ///     validator path), with the SIMPLE/COMPLEX core-label distinction.
    /// * `BlockingSignatureCacheType`: a cache is built only when `CACHED` AND the
    ///   ontology has no nominals AND the strategy is not a core one.
    ///
    /// The validator itself (for the core strategies) is attached separately by
    /// the reasoner via [`set_blocking_validator`]; this method records whether a
    /// core strategy is selected so the reasoner knows to attach it.
    pub fn configure_blocking(
        &mut self,
        configuration: &crate::configuration::Configuration,
        has_inverse_roles: bool,
        has_nominals: bool,
    ) {
        use crate::configuration::{BlockingSignatureCacheType, BlockingStrategyType, DirectBlockingType};
        use crate::tableau::blocking_strategy::{BlockingStrategyKind, DirectBlockingKind};

        let is_core = matches!(
            configuration.blocking_strategy_type,
            BlockingStrategyType::SimpleCore | BlockingStrategyType::ComplexCore
        );

        self.blocking_has_inverses = has_inverse_roles;

        // --- directBlockingChecker switch ---
        // The core (validated) strategies always use the single (validated) label
        // signature in Java (ValidatedSingleDirectBlockingChecker / Pairwise); the
        // Rust validated path uses the core atomic-concept label, so the direct
        // kind is informational for the non-core strategies.
        self.direct_blocking_kind = match configuration.direct_blocking_type {
            // OPTIMAL: a core strategy uses the validated single label; otherwise
            // pairwise iff the ontology has inverse roles (where single blocking is
            // incomplete), else single. Mirrors Reasoner.java:1968-1977.
            DirectBlockingType::Optimal if is_core => DirectBlockingKind::Single,
            DirectBlockingType::Optimal if has_inverse_roles => DirectBlockingKind::Pairwise,
            DirectBlockingType::Optimal => DirectBlockingKind::Single,
            DirectBlockingType::Single => DirectBlockingKind::Single,
            DirectBlockingType::PairWise => DirectBlockingKind::Pairwise,
        };

        // --- blockingStrategy switch ---
        self.blocking_strategy_kind = match configuration.blocking_strategy_type {
            BlockingStrategyType::Ancestor => BlockingStrategyKind::Ancestor,
            BlockingStrategyType::Anywhere | BlockingStrategyType::Optimal => {
                BlockingStrategyKind::Anywhere
            }
            // SIMPLE_CORE / COMPLEX_CORE -> the validated/core path. The validator
            // (which makes `is_exact()` false) is attached by the reasoner; the
            // strategy kind is recorded so `compute_blocking_with` routes through
            // the validated pass.
            BlockingStrategyType::SimpleCore => BlockingStrategyKind::ValidatedCore { simple: true },
            BlockingStrategyType::ComplexCore => {
                BlockingStrategyKind::ValidatedCore { simple: false }
            }
        };

        // --- blockingSignatureCache switch ---
        // Java: cache built only when !hasNominals && !core, and CACHED.
        self.blocking_signature_cache = if !has_nominals
            && !is_core
            && configuration.blocking_signature_cache_type == BlockingSignatureCacheType::Cached
        {
            Some(crate::blocking::BlockingSignatureCache::new())
        } else {
            None
        };
    }

    /// Whether the configured blocking strategy is a core/validated one (so the
    /// reasoner must attach a [`BlockingValidator`]).
    pub fn blocking_uses_validator(&self) -> bool {
        matches!(
            self.blocking_strategy_kind,
            crate::tableau::blocking_strategy::BlockingStrategyKind::ValidatedCore { .. }
        )
    }

    /// Whether the configured core strategy is the SIMPLE-core variant (vs the
    /// COMPLEX-core variant). Meaningful only when [`blocking_uses_validator`].
    pub fn blocking_core_is_simple(&self) -> bool {
        matches!(
            self.blocking_strategy_kind,
            crate::tableau::blocking_strategy::BlockingStrategyKind::ValidatedCore { simple: true }
        )
    }

    /// Port of `Tableau.updateFlagsDependentOnAdditionalOntology`: decide which of
    /// `owl:Thing` / `internal:named` / `rdfs:Literal` must be materialized on every
    /// node, from whether the hyperresolution manager has a clause consuming that
    /// predicate in its delta. Must be called *before* any node is created, since
    /// node creation seeds these assertions gated on these flags. Without this, a
    /// `C(X) :- owl:Thing(X)` top-GCI never fires.
    pub fn update_extension_flags(
        &mut self,
        manager: &crate::tableau::HyperresolutionManager,
    ) {
        self.needs_thing_extension = manager.needs_thing_extension();
        self.needs_named_extension = manager.needs_named_extension();
        self.needs_rdfs_literal_extension = manager.needs_rdfs_literal_extension();
    }

    /// `updateFlagsDependentOnAdditionalOntology` (Tableau.java:248-251): OR the
    /// node-seeding flags with those of an additional hyperresolution manager, so a
    /// delta clause consuming `owl:Thing`/`internal:named`/`rdfs:Literal` still seeds
    /// the corresponding extension even when the permanent KB does not.
    pub fn merge_extension_flags(
        &mut self,
        manager: &crate::tableau::HyperresolutionManager,
    ) {
        self.needs_thing_extension |= manager.needs_thing_extension();
        self.needs_named_extension |= manager.needs_named_extension();
        self.needs_rdfs_literal_extension |= manager.needs_rdfs_literal_extension();
    }

    /// Port of `ExistentialExpansionManager.updateFunctionalRoles` (which calls
    /// `loadDLClausesIntoGraph`). Builds the functional-role map from the
    /// permanent DL clauses and stores it on the tableau so existential expansion
    /// can try a functional expansion before a normal one.
    ///
    /// HermiT computes this in the `ExistentialExpansionManager` constructor from
    /// `m_tableau.m_permanentDLOntology.getDLClauses()`. In this port the reasoner
    /// owns the `DLOntology`, so it must call this method once when it builds the
    /// tableau -- a one-line call alongside the existing
    /// `tableau.update_extension_flags(&manager)`:
    ///
    /// ```ignore
    /// tableau.set_functional_roles_from_clauses(self.dl_ontology.get_dl_clauses());
    /// ```
    ///
    /// Were the map left empty, every role would be treated as non-functional and
    /// existential expansion would still give the same answers (the at-most rule
    /// recovers them); the populated map makes the tableau shape and clash timing
    /// match HermiT.
    pub fn set_functional_roles_from_clauses(
        &mut self,
        dl_clauses: &indexmap::IndexSet<crate::model::DLClause>,
    ) {
        use crate::graph::Graph;
        use crate::model::Role;
        use rustc_hash::FxHashSet as HashSet;

        // loadDLClausesIntoGraph: build the super-role graph and the set of
        // (directly) functional roles from the clauses.
        let mut super_role_graph: Graph<Role> = Graph::new();
        let mut functional_roles: HashSet<Role> = HashSet::default();
        for dl_clause in dl_clauses {
            if dl_clause.is_atomic_role_inclusion() {
                let subrole = Self::body_atomic_role(dl_clause, 0);
                let superrole = Self::head_atomic_role(dl_clause, 0);
                if let (Some(subrole), Some(superrole)) = (subrole, superrole) {
                    super_role_graph
                        .add_edge(Role::AtomicRole(subrole.clone()), Role::AtomicRole(superrole.clone()));
                    super_role_graph.add_edge(subrole.get_inverse(), superrole.get_inverse());
                }
            } else if dl_clause.is_atomic_role_inverse_inclusion() {
                let subrole = Self::body_atomic_role(dl_clause, 0);
                let superrole = Self::head_atomic_role(dl_clause, 0);
                if let (Some(subrole), Some(superrole)) = (subrole, superrole) {
                    super_role_graph.add_edge(Role::AtomicRole(subrole.clone()), superrole.get_inverse());
                    super_role_graph
                        .add_edge(subrole.get_inverse(), Role::AtomicRole(superrole.clone()));
                }
            } else if dl_clause.is_functionality_axiom() {
                if let Some(atomic_role) = Self::body_atomic_role(dl_clause, 0) {
                    functional_roles.insert(Role::AtomicRole(atomic_role.clone()));
                }
            } else if dl_clause.is_inverse_functionality_axiom() {
                if let Some(atomic_role) = Self::body_atomic_role(dl_clause, 0) {
                    functional_roles.insert(atomic_role.get_inverse());
                }
            }
        }

        // updateFunctionalRoles: reflexively close (each role and its inverse are
        // their own super-role), then transitively close.
        for role in super_role_graph.get_elements().clone() {
            super_role_graph.add_edge(role.clone(), role.clone());
            super_role_graph.add_edge(role.get_inverse(), role.get_inverse());
        }
        super_role_graph.transitively_close();
        let sub_role_graph = super_role_graph.get_inverse();

        // For each role, the relevant roles are the sub-roles of any functional
        // super-role; if non-empty, the role gets an entry in the functional map.
        self.functional_roles.clear();
        for role in super_role_graph.get_elements().clone() {
            let mut relevant_roles: HashSet<Role> = HashSet::default();
            for superrole in super_role_graph.get_successors(&role) {
                if functional_roles.contains(&superrole) {
                    for subrole in sub_role_graph.get_successors(&superrole) {
                        relevant_roles.insert(subrole);
                    }
                }
            }
            if !relevant_roles.is_empty() {
                self.functional_roles
                    .insert(role, relevant_roles.into_iter().collect());
            }
        }
    }

    /// Extracts the body atom's predicate as an `AtomicRole`, if it is one.
    fn body_atomic_role(
        dl_clause: &crate::model::DLClause,
        index: usize,
    ) -> Option<crate::model::AtomicRole> {
        match dl_clause.get_body_atom(index).get_dl_predicate() {
            crate::model::DLPredicate::AtomicRole(r) => Some(r.clone()),
            _ => None,
        }
    }

    /// Extracts the head atom's predicate as an `AtomicRole`, if it is one.
    fn head_atomic_role(
        dl_clause: &crate::model::DLClause,
        index: usize,
    ) -> Option<crate::model::AtomicRole> {
        match dl_clause.get_head_atom(index).get_dl_predicate() {
            crate::model::DLPredicate::AtomicRole(r) => Some(r.clone()),
            _ => None,
        }
    }

    /// Directly seed the functional-role map (used by tests and by any caller
    /// that has already computed the relevant-role sets). Mirrors a single
    /// `m_functionalRoles.put(role, relevantRoles)`.
    #[cfg(test)]
    pub(crate) fn set_functional_role_entry_for_test(
        &mut self,
        role: crate::model::Role,
        relevant_roles: Vec<crate::model::Role>,
    ) {
        self.functional_roles.insert(role, relevant_roles);
    }

    pub fn dependency_set_factory(&mut self) -> &mut DependencySetFactory {
        &mut self.dependency_set_factory
    }

    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id]
    }
    pub fn node_mut(&mut self, id: NodeId) -> &mut Node {
        &mut self.nodes[id]
    }

    // -- Node creation -------------------------------------------------------

    pub fn create_new_named_node(&mut self, dependency_set: &DependencySet) -> NodeId {
        self.create_new_node_raw(dependency_set, None, NodeType::NamedNode, 0)
    }
    pub fn create_new_ni_node(&mut self, dependency_set: &DependencySet) -> NodeId {
        self.create_new_node_raw(dependency_set, None, NodeType::NiNode, 0)
    }
    pub fn create_new_tree_node(&mut self, dependency_set: &DependencySet, parent: NodeId) -> NodeId {
        let depth = self.nodes[parent].tree_depth + 1;
        self.create_new_node_raw(dependency_set, Some(parent), NodeType::TreeNode, depth)
    }
    pub fn create_new_concrete_node(
        &mut self,
        dependency_set: &DependencySet,
        parent: NodeId,
    ) -> NodeId {
        let depth = self.nodes[parent].tree_depth + 1;
        self.create_new_node_raw(dependency_set, Some(parent), NodeType::ConcreteNode, depth)
    }
    pub fn create_new_root_constant_node(&mut self, dependency_set: &DependencySet) -> NodeId {
        self.create_new_node_raw(dependency_set, None, NodeType::RootConstantNode, 0)
    }
    pub fn create_new_graph_node(
        &mut self,
        parent: Option<NodeId>,
        dependency_set: &DependencySet,
    ) -> NodeId {
        let depth = parent.map(|p| self.nodes[p].tree_depth).unwrap_or(0);
        self.create_new_node_raw(dependency_set, parent, NodeType::GraphNode, depth)
    }

    fn allocate_node(&mut self) -> NodeId {
        if let Some(reused) = self.first_free_node {
            self.first_free_node = self.nodes[reused].next_free_node;
            self.nodes[reused].next_free_node = None;
            reused
        } else {
            self.allocated_nodes += 1;
            self.nodes.push(Node::new_empty());
            self.nodes.len() - 1
        }
    }

    fn create_new_node_raw(
        &mut self,
        dependency_set: &DependencySet,
        parent: Option<NodeId>,
        node_type: NodeType,
        tree_depth: i32,
    ) -> NodeId {
        let node = self.allocate_node();
        debug_assert_eq!(self.nodes[node].node_id, -1);
        debug_assert!(self.nodes[node].node_state.is_none());

        self.number_of_nodes_in_tableau += 1;
        self.initialize_node(node, self.number_of_nodes_in_tableau, parent, node_type, tree_depth);
        // The ExistentialExpansionStrategy.nodeInitialized callback is not forwarded.

        let last = self.last_tableau_node;
        self.nodes[node].previous_tableau_node = last;
        match last {
            None => self.first_tableau_node = Some(node),
            Some(last) => self.nodes[last].next_tableau_node = Some(node),
        }
        self.last_tableau_node = Some(node);
        // ExistentialExpansionStrategy.nodeStatusChanged -> AnywhereBlocking marks
        // the fresh node changed so incremental blocking reprocesses it.
        self.note_blocking_node_changed(node);
        // AnywhereValidatedBlocking.nodeStatusChanged also marks the node itself and
        // its parent as having changed since the last block validation.
        self.validation_info_changed_self(node);
        self.validation_info_changed_parent(node);
        // A fresh data node (which may carry an ill-typed constant) must be seen
        // by the next datatype check.
        if !node_type.is_abstract() {
            self.datatype_check_needed = true;
        }
        self.number_of_node_creations += 1;
        self.monitor_event(|m| m.node_created()); // Port of tableau_monitor.nodeCreated(node)

        // Seed the THING / INTERNAL_NAMED / RDFS_LITERAL assertions.
        use crate::model::{AtomicConcept, Concept, DLPredicate, InternalDatatype};
        if node_type.is_abstract() {
            let thing = Concept::AtomicConcept(AtomicConcept::thing().clone());
            self.add_concept_assertion(thing, node, dependency_set, true);
            if node_type == NodeType::NamedNode && self.needs_named_extension {
                let named = Concept::AtomicConcept(AtomicConcept::internal_named().clone());
                self.add_concept_assertion(named, node, dependency_set, true);
            }
        } else {
            let rdfs_literal =
                DLPredicate::InternalDatatype(InternalDatatype::rdfs_literal().clone());
            self.add_dl_predicate_assertion(rdfs_literal, node, dependency_set, true);
        }
        node
    }

    fn initialize_node(
        &mut self,
        node: NodeId,
        node_id: i32,
        parent: Option<NodeId>,
        node_type: NodeType,
        tree_depth: i32,
    ) {
        let n = &mut self.nodes[node];
        n.node_id = node_id;
        n.node_state = Some(NodeState::Active);
        n.parent = parent;
        n.node_type = node_type;
        n.tree_depth = tree_depth;
        n.number_of_positive_atomic_concepts = 0;
        n.number_of_negated_atomic_concepts = 0;
        n.number_of_negated_role_assertions = 0;
        n.unprocessed_existentials.clear();
        n.previous_tableau_node = None;
        n.next_tableau_node = None;
        n.previous_merged_or_pruned_node = None;
        n.merged_into = None;
        n.merged_into_dependency_set = None;
        n.blocker = None;
        n.directly_blocked = false;
        n.constant_value = None;
        // Port of Node constructor -> m_descriptionGraphManager.intializeNode
        // (Node.java:86). The borrow of `n` ends here, so the manager call (which
        // borrows the manager field, not `nodes`) is split out.
        self.description_graph_manager.initialize_node(node);
    }

    // -- Merge / prune / backtrack ------------------------------------------

    pub fn merge_node(&mut self, node: NodeId, merge_into: NodeId, dependency_set: &DependencySet) {
        debug_assert_eq!(self.nodes[node].node_state, Some(NodeState::Active));
        let permanent = self.dependency_set_factory.get_permanent(dependency_set);
        self.dependency_set_factory.add_usage(&permanent);
        let n = &mut self.nodes[node];
        n.merged_into = Some(merge_into);
        n.merged_into_dependency_set = Some(permanent);
        n.node_state = Some(NodeState::Merged);
        n.previous_merged_or_pruned_node = self.last_merged_or_pruned_node;
        self.last_merged_or_pruned_node = Some(node);
        self.number_of_merged_or_pruned_nodes += 1;
        // ExistentialExpansionStrategy.nodeStatusChanged (nodesMerged itself is a
        // no-op for the anywhere blocking checkers).
        self.note_blocking_node_changed(node);
        // AnywhereValidatedBlocking.nodeStatusChanged marks the node itself and its
        // parent; nodesMerged additionally marks the parent (idempotent here).
        self.validation_info_changed_self(node);
        self.validation_info_changed_parent(node);
    }

    pub fn prune_node(&mut self, node: NodeId) {
        debug_assert_eq!(self.nodes[node].node_state, Some(NodeState::Active));
        let n = &mut self.nodes[node];
        n.node_state = Some(NodeState::Pruned);
        n.previous_merged_or_pruned_node = self.last_merged_or_pruned_node;
        self.last_merged_or_pruned_node = Some(node);
        self.number_of_merged_or_pruned_nodes += 1;
        // ExistentialExpansionStrategy.nodeStatusChanged.
        self.note_blocking_node_changed(node);
        // AnywhereValidatedBlocking.nodeStatusChanged also marks the node itself and
        // its parent.
        self.validation_info_changed_self(node);
        self.validation_info_changed_parent(node);
    }

    pub(crate) fn backtrack_last_merged_or_pruned_node(&mut self) {
        let node = self.last_merged_or_pruned_node.expect("no merged/pruned node");
        if self.nodes[node].node_state == Some(NodeState::Merged) {
            if let Some(dependency_set) = self.nodes[node].merged_into_dependency_set.clone() {
                self.dependency_set_factory.remove_usage(&dependency_set);
            }
            self.nodes[node].merged_into = None;
            self.nodes[node].merged_into_dependency_set = None;
        }
        self.nodes[node].node_state = Some(NodeState::Active);
        self.last_merged_or_pruned_node = self.nodes[node].previous_merged_or_pruned_node;
        self.nodes[node].previous_merged_or_pruned_node = None;
        self.number_of_merged_or_pruned_nodes -= 1;
        // ExistentialExpansionStrategy.nodeStatusChanged (nodesUnmerged itself is a
        // no-op for the anywhere blocking checkers).
        self.note_blocking_node_changed(node);
        // AnywhereValidatedBlocking.nodeStatusChanged marks the node itself and its
        // parent; nodesUnmerged additionally marks the parent (idempotent here).
        self.validation_info_changed_self(node);
        self.validation_info_changed_parent(node);
    }

    pub(crate) fn destroy_last_tableau_node(&mut self) {
        let node = self.last_tableau_node.expect("no tableau node");
        debug_assert_eq!(self.nodes[node].node_state, Some(NodeState::Active));
        // ExistentialExpansionStrategy.nodeDestroyed: drop the node from the
        // blockers cache and roll `first_changed_node` back past it.
        self.note_blocking_node_destroyed(node);
        match self.nodes[node].previous_tableau_node {
            None => self.first_tableau_node = None,
            Some(prev) => self.nodes[prev].next_tableau_node = None,
        }
        self.last_tableau_node = self.nodes[node].previous_tableau_node;
        self.destroy_node(node);
        self.nodes[node].next_free_node = self.first_free_node;
        self.first_free_node = Some(node);
        self.number_of_nodes_in_tableau -= 1;
        self.monitor_event(|m| m.node_destroyed()); // Port of tableau_monitor.nodeDestroyed(node)
    }

    fn destroy_node(&mut self, node: NodeId) {
        if let Some(dependency_set) = self.nodes[node].merged_into_dependency_set.clone() {
            self.dependency_set_factory.remove_usage(&dependency_set);
        }
        let n = &mut self.nodes[node];
        n.node_id = -1;
        n.node_state = None;
        n.parent = None;
        n.unprocessed_existentials.clear();
        n.previous_tableau_node = None;
        n.next_tableau_node = None;
        n.previous_merged_or_pruned_node = None;
        n.merged_into = None;
        n.merged_into_dependency_set = None;
        n.blocker = None;
        // Port of Node.destroy -> m_descriptionGraphManager.destroyNode
        // (Node.java:107): return the node's graph-occurrence records to the
        // free list.
        self.description_graph_manager.destroy_node(node);
    }

    // -- Accessors / traversals (the Node methods needing the arena) --------

    pub fn get_first_tableau_node(&self) -> Option<NodeId> {
        self.first_tableau_node
    }
    pub fn get_last_tableau_node(&self) -> Option<NodeId> {
        self.last_tableau_node
    }
    pub fn get_number_of_node_creations(&self) -> i32 {
        self.number_of_node_creations
    }
    pub fn get_number_of_nodes_in_tableau(&self) -> i32 {
        self.number_of_nodes_in_tableau
    }

    pub fn get_node(&self, node_id: i32) -> Option<NodeId> {
        let mut node = self.first_tableau_node;
        while let Some(id) = node {
            if self.nodes[id].node_id == node_id {
                return Some(id);
            }
            node = self.nodes[id].next_tableau_node;
        }
        None
    }

    /// The Java `Node.getCanonicalNode` (follows merge pointers).
    pub fn get_canonical_node(&self, node: NodeId) -> NodeId {
        let mut result = node;
        while let Some(merged_into) = self.nodes[result].merged_into {
            result = merged_into;
        }
        result
    }

    /// The Java `Node.isAncestorOf`.
    pub fn is_ancestor_of(&self, ancestor: NodeId, potential_descendant: NodeId) -> bool {
        let mut current = Some(potential_descendant);
        while let Some(node) = current {
            current = self.nodes[node].parent;
            if current == Some(ancestor) {
                return true;
            }
        }
        false
    }

    // -- Read-only accessors for the interactive debugger -------------------
    //
    // These expose tableau state the `debugger::Debugger` commands read (the
    // node label / extension-table tuples / unprocessed ground disjunctions /
    // clash flag). They are pure reads -- they never mutate the tableau and so
    // cannot change any reasoning answer. They mirror what HermiT's `Debugger`
    // reaches through `m_tableau.getExtensionManager()...` and
    // `getFirstUnprocessedGroundDisjunction()`.

    /// `Tableau.getNumberOfNodesInTableau` exposed as a plain count for
    /// `modelStats` (number of nodes currently on the tableau node list).
    pub fn debug_node_count(&self) -> i32 {
        self.number_of_nodes_in_tableau
    }

    /// The atomic concepts (positive, non-core and core combined) asserted on
    /// `node`, as predicate-aware label strings, sorted. Backs `showNode`'s
    /// positive concept label. Reads the binary extension table (TOTAL view).
    pub fn debug_node_atomic_concept_labels(
        &self,
        node: NodeId,
        prefixes: &crate::prefixes::Prefixes,
    ) -> Vec<String> {
        let retrieval = self.create_binary_retrieval(
            [-1, 1],
            [None, Some(crate::tableau::object::TableauObject::Node(node))],
            crate::tableau::extension_table::View::Total,
        );
        let mut labels = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            if let crate::tableau::object::TableauObject::Concept(
                crate::model::Concept::AtomicConcept(c),
            ) = self.binary_extension_table.get_tuple_object(tuple_index, 0)
            {
                labels.push(c.to_string_prefixes(prefixes));
            }
        }
        labels.sort();
        labels
    }

    /// Every binary-table assertion (concept-like label + node id), as
    /// `label[id]` strings. Backs `showModel`'s binary tuples.
    /// Every binary-table assertion as `(display, sort_predicate)` pairs.
    /// `display` is `predicate[id]` rendered with `prefixes` (Java's `printFact`
    /// uses `m_debugger.getPrefixes()`); `sort_predicate` is the predicate
    /// rendered with the standard prefixes, the key `Printing.FactComparator`
    /// orders by (it compares `predicate.toString()`, the no-arg `toString` that
    /// abbreviates against the standard prefixes). Unsorted: `showModel` applies
    /// the `FactComparator` order itself.
    pub fn debug_binary_facts(
        &self,
        prefixes: &crate::prefixes::Prefixes,
    ) -> Vec<(String, String)> {
        use crate::tableau::object::TableauObject;
        let standard = crate::prefixes::Prefixes::standard();
        let retrieval = self.create_binary_retrieval(
            [-1, -1],
            [None, None],
            crate::tableau::extension_table::View::Total,
        );
        let mut facts = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            let (label, sort_label) = match self.binary_extension_table.get_tuple_object(tuple_index, 0) {
                TableauObject::Concept(c) => (c.to_string_prefixes(prefixes), c.to_string_prefixes(standard)),
                TableauObject::DLPredicate(p) => (p.to_string_prefixes(prefixes), p.to_string_prefixes(standard)),
                TableauObject::NegatedAtomicRole(r) => (r.to_string_prefixes(prefixes), r.to_string_prefixes(standard)),
                TableauObject::DescriptionGraph(g) => (g.to_string_prefixes(prefixes), g.to_string_prefixes(standard)),
                TableauObject::Node(_) => continue,
            };
            let id = self.binary_extension_table
                .get_tuple_object(tuple_index, 1)
                .as_node()
                .map(|n| self.nodes[n].node_id)
                .unwrap_or(-1);
            facts.push((format!("{label}[{id}]"), sort_label));
        }
        facts
    }

    /// Every ternary-table assertion (predicate + two node ids), as
    /// `predicate[id1,id2]` strings. Backs `showModel`'s ternary tuples.
    pub fn debug_ternary_facts(
        &self,
        prefixes: &crate::prefixes::Prefixes,
    ) -> Vec<(String, String)> {
        use crate::tableau::object::TableauObject;
        let standard = crate::prefixes::Prefixes::standard();
        let retrieval = self.create_ternary_retrieval(
            [-1, -1, -1],
            [None, None, None],
            crate::tableau::extension_table::View::Total,
        );
        let mut facts = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            let (label, sort_label) = match self.ternary_extension_table.get_tuple_object(tuple_index, 0) {
                TableauObject::DLPredicate(p) => (p.to_string_prefixes(prefixes), p.to_string_prefixes(standard)),
                TableauObject::NegatedAtomicRole(r) => (r.to_string_prefixes(prefixes), r.to_string_prefixes(standard)),
                TableauObject::Concept(c) => (c.to_string_prefixes(prefixes), c.to_string_prefixes(standard)),
                TableauObject::DescriptionGraph(g) => (g.to_string_prefixes(prefixes), g.to_string_prefixes(standard)),
                TableauObject::Node(_) => continue,
            };
            let id1 = self.ternary_extension_table
                .get_tuple_object(tuple_index, 1)
                .as_node()
                .map(|n| self.nodes[n].node_id)
                .unwrap_or(-1);
            let id2 = self.ternary_extension_table
                .get_tuple_object(tuple_index, 2)
                .as_node()
                .map(|n| self.nodes[n].node_id)
                .unwrap_or(-1);
            facts.push((format!("{label}[{id1},{id2}]"), sort_label));
        }
        facts
    }

    /// `Tableau.getFirstUnprocessedGroundDisjunction` rendered as one string per
    /// disjunction (most-recent first, following `getPreviousGroundDisjunction`),
    /// matching `UnprocessedDisjunctionsCommand`'s `d0 v d1 v ...` layout. Backs
    /// `uDisjunctions`.
    pub fn debug_unprocessed_ground_disjunctions(
        &self,
        prefixes: &crate::prefixes::Prefixes,
    ) -> Vec<String> {
        let mut out = Vec::new();
        let mut current = self.first_unprocessed_ground_disjunction;
        while let Some(index) = current {
            let disjunction = match &self.ground_disjunctions[index] {
                Some(disjunction) => disjunction,
                None => break,
            };
            out.push(self.format_ground_disjunction(disjunction, prefixes));
            // `getPreviousGroundDisjunction` walk (the active-list link).
            current = disjunction.previous;
        }
        out
    }

    fn format_ground_disjunction(
        &self,
        disjunction: &crate::tableau::branching::GroundDisjunctionData,
        prefixes: &crate::prefixes::Prefixes,
    ) -> String {
        use crate::model::DLPredicate;
        let header = self
            .ground_disjunction_header_manager
            .header(disjunction.header_index);
        let predicates = header.dl_predicates();
        let mut buffer = String::new();
        for (disjunct_index, dl_predicate) in predicates.iter().enumerate() {
            if disjunct_index != 0 {
                buffer.push_str(" v ");
            }
            let start = header.disjunct_start(disjunct_index);
            if matches!(dl_predicate, DLPredicate::Equality) {
                let a0 = self.nodes[disjunction.arguments[start]].node_id;
                let a1 = self.nodes[disjunction.arguments[start + 1]].node_id;
                buffer.push_str(&format!("{a0} == {a1}"));
            } else {
                buffer.push_str(&dl_predicate.to_string_prefixes(prefixes));
                buffer.push('(');
                for argument_index in 0..dl_predicate.arity() {
                    if argument_index != 0 {
                        buffer.push(',');
                    }
                    let id = self.nodes[disjunction.arguments[start + argument_index]].node_id;
                    buffer.push_str(&id.to_string());
                }
                buffer.push(')');
            }
        }
        buffer
    }

    /// The Java `Node.addCanonicalNodeDependencySet`.
    pub fn add_canonical_node_dependency_set(
        &mut self,
        node: NodeId,
        dependency_set: &DependencySet,
    ) -> PermanentDependencySet {
        let mut result = self.dependency_set_factory.get_permanent(dependency_set);
        let mut current = node;
        while let Some(merged_into) = self.nodes[current].merged_into {
            let merged_dependency_set = self.nodes[current]
                .merged_into_dependency_set
                .clone()
                .expect("merged node has a dependency set");
            result = self.dependency_set_factory.union_with(
                &DependencySet::Permanent(result),
                &DependencySet::Permanent(merged_dependency_set),
            );
            current = merged_into;
        }
        result
    }

    /// Faithful port of `Tableau.clear()` (Tableau.java:182-211): resets all
    /// PER-TEST state so one configured tableau can be reused across many
    /// satisfiability tests, then fires `tableauCleared`. PERMANENT
    /// (ontology/clause-derived, set-once) state is deliberately left intact:
    /// `functional_roles`, the datatype config flags (`check_datatypes`,
    /// `check_unknown_datatype_restrictions`, `unknown_datatype_restrictions`),
    /// the blocking config (`blocking_validator`, `blocking_strategy_kind`,
    /// `direct_blocking_kind`, `blocking_has_inverses`, and the signature cache,
    /// which persists across tests in HermiT), the description-graph *definitions*,
    /// the node-seeding flags (`needs_*_extension`), the `ground_disjunction_header_
    /// manager` (interned headers are part of the permanent hyperresolution
    /// manager, whose `clear()` does NOT reset compiled programs / interned
    /// headers), and the configuration-derived flags (`use_disjunction_learning`,
    /// `existential_strategy_type`, interrupt/monitor).
    pub fn clear(&mut self) {
        // m_allocatedNodes=0; m_numberOf...=0; node-list heads = null.
        self.allocated_nodes = 0;
        self.number_of_nodes_in_tableau = 0;
        self.number_of_merged_or_pruned_nodes = 0;
        self.number_of_node_creations = 0;
        self.first_free_node = None;
        self.first_tableau_node = None;
        self.last_tableau_node = None;
        self.last_merged_or_pruned_node = None;
        // The node arena: Java keeps the `Node` objects on a free list and reuses
        // them; here the arena is a `Vec` that the (now-empty) free/tableau lists
        // no longer reference, so dropping it is the faithful reset.
        self.nodes.clear();

        // m_firstGroundDisjunction=null; m_firstUnprocessedGroundDisjunction=null.
        self.ground_disjunctions.clear();
        self.first_ground_disjunction = None;
        self.first_unprocessed_ground_disjunction = None;

        // m_branchingPoints=new BranchingPoint[2]; m_currentBranchingPoint=-1;
        // m_nonbacktrackableBranchingPoint=-1.
        self.branching_points.clear();
        self.current_branching_point = -1;
        self.nonbacktrackable_branching_point = -1;

        // m_dependencySetFactory.clear().
        self.dependency_set_factory.clear();

        // m_extensionManager.clear(): the two extension tables + the clash set.
        self.binary_extension_table.clear();
        self.ternary_extension_table.clear();
        self.clash_dependency_set = None;
        self.add_active = false;

        // m_clashManager.clear(): only transient aux tuples in Java; no per-test
        // field of its own lives on this struct.

        // m_permanentHyperresolutionManager.clear() (+ additional if present):
        // the Rust HyperresolutionManager holds only the compiled programs and is
        // owned by the reasoner, not this struct; its `clear()` resets only
        // transient buffers, so there is nothing per-test to reset here.

        // m_mergingManager.clear(): only transient search/aux tuples in Java.

        // m_existentialExpasionManager.clear(): m_expandedExistentials and the
        // per-branching-point watermark (Rust keeps these on the tableau).
        self.expanded_existentials.clear();
        self.expanded_existentials_by_branching_point.clear();

        // m_nominalIntroductionManager.clear(): the annotated-equality buffer + its
        // read cursor + the NI-root dedup index (`m_newRootNodesTable`/`Index`).
        self.annotated_equalities.clear();
        self.first_unprocessed_annotated_equality = 0;
        self.annotated_equalities_by_branching_point.clear();
        self.first_unprocessed_ae_by_branching_point.clear();
        self.ni_roots.clear();
        self.ni_roots_log.clear();
        self.ni_roots_by_branching_point.clear();

        // m_descriptionGraphManager.clear(): per-test work state only (keeps the
        // graph definitions).
        self.description_graph_manager.clear();

        // m_isCurrentModelDeterministic=true: in this port the deterministic-model
        // flag is recomputed per run from `is_deterministic()`/the strategy, and the
        // datatype-check cursor is reset so the first check of the next test runs.
        self.datatype_check_needed = true;

        // m_existentialExpansionStrategy.clear(): the incremental anywhere-blocking
        // state and the (validated) blockers caches. The blocking *signature* cache
        // persists (permanent) -- only the per-run blockers caches reset here.
        self.first_changed_node = None;
        self.last_validated_unchanged_node = None;
        self.blockers_cache_by_signature.clear();
        self.blockers_cache_node_signature.clear();
        self.validated_blockers_by_signature.clear();
        self.validated_blockers_node_signature.clear();
        // (The `BlockingValidator`, when attached, holds only permanent
        // clause-derived state; the per-node validation flags
        // (`block_violates_parent_constraints`) live on `Node` and are dropped with
        // the node arena above, so the validator itself needs no `clear()`.)
        // The IndividualReuseStrategy's per-run state (re-seeds dont_reuse_this_run
        // from the shared ever-set); a no-op for the default creation-order strategy.
        if let Some(strategy) = self.individual_reuse_strategy.as_mut() {
            strategy.clear();
        }

        // m_datatypeManager.clear(): only transient buffers in Java; no per-test
        // field of its own on this struct (the unknown-restriction set is permanent).

        // m_existentialConceptsBuffers.clear(): a transient scratch buffer in Java;
        // not a stored field in this port.

        // Reset the per-run interrupt latch to its fresh-build state (a
        // Rust-specific field with no Java analogue); a stale interrupt from a
        // previous test must not leak into the reused tableau.
        self.pending_interrupt = None;

        // m_tableauMonitor.tableauCleared().
        self.monitor_event(|m| m.tableau_cleared());
    }
}

/// Port of the `Reasoner.createTableau` `switch(tableauMonitorType)`
/// (Reasoner.java ~1940-1957) that builds the well-known tableau monitor:
///   * `NONE`              -> no monitor (`null`).
///   * `TIMING`            -> `new Timer()`            (here a [`Timer`] over stdout).
///   * `TIMING_WITH_PAUSE` -> `new TimerWithPause()`   (a [`TimerWithPause`] over
///     stdout/stdin).
///   * `DEBUGGER_HISTORY_ON` / `DEBUGGER_NO_HISTORY` -> `new Debugger(prefixes,_)`.
///
/// The `Timer`/`TimerWithPause` monitors are answer-neutral observers (they only
/// print statistics), so selecting them never changes a reasoning result.
///
/// The `DEBUGGER_*` variants map to HermiT's interactive `Debugger` console (a
/// full command-line REPL over the tableau with prefix rendering), which is not
/// ported -- there is no `Debugger` type in the Rust monitor module. They
/// therefore fall back to `None` (no monitor), behaviourally identical to `NONE`
/// for the reasoning result.
fn default_monitor_for(
    monitor_type: crate::configuration::TableauMonitorType,
) -> Option<Box<dyn crate::monitor::TableauMonitor>> {
    use crate::configuration::TableauMonitorType;
    match monitor_type {
        TableauMonitorType::None => None,
        // HermiT's CLI wires the `Timer` monitor to `System.err`
        // (CommandLine.java:730), keeping its statistics off the result stream.
        TableauMonitorType::Timing => {
            Some(Box::new(crate::monitor::Timer::new(std::io::stderr())))
        }
        TableauMonitorType::TimingWithPause => Some(Box::new(
            crate::monitor::TimerWithPause::new(
                std::io::stderr(),
                std::io::BufReader::new(std::io::stdin()),
            ),
        )),
        // The interactive Debugger console is not ported; fall back to
        // no monitor (answer-neutral, identical to NONE).
        TableauMonitorType::DebuggerNoHistory | TableauMonitorType::DebuggerHistoryOn => None,
    }
}

impl Default for Tableau {
    fn default() -> Self {
        Tableau::new()
    }
}

#[cfg(test)]
mod config_tests {
    use super::*;
    use crate::configuration::Configuration;

    #[test]
    fn default_configuration_preserves_behaviour() {
        // The default tableau has disjunction-learning on, no monitor,
        // and a never-firing interrupt flag.
        let mut tableau = Tableau::new();
        assert!(tableau.use_disjunction_learning);
        assert!(tableau.monitor.is_none());
        tableau.start_task();
        tableau.note_interrupt();
        assert!(tableau.take_pending_interrupt().is_none());
        tableau.end_task();
    }

    #[test]
    fn configuration_disables_disjunction_learning() {
        let mut config = Configuration::default();
        config.use_disjunction_learning = false;
        let tableau = Tableau::with_configuration(&config);
        assert!(!tableau.use_disjunction_learning);
    }

    #[test]
    fn positive_timeout_latches_a_pending_interrupt() {
        // With a 1ms timeout, note_interrupt latches a Timeout once the task
        // has run past the deadline; the default -1 never does (above).
        let mut config = Configuration::default();
        config.individual_task_timeout = 1;
        let mut tableau = Tableau::with_configuration(&config);
        tableau.start_task();
        std::thread::sleep(std::time::Duration::from_millis(10));
        tableau.note_interrupt();
        assert_eq!(
            tableau.take_pending_interrupt(),
            Some(crate::tableau::interrupt_flag::InterruptError::Timeout)
        );
        tableau.end_task();
    }

    #[test]
    fn default_strategy_is_exact_and_creation_order() {
        // The default pairwise blocking strategy is exact, so the runCalculus
        // final-chance branch is dead. The default existential strategy is
        // CreationOrder with no reuse object.
        let tableau = Tableau::new();
        assert!(tableau.is_exact(), "default pairwise blocking must be exact");
        assert_eq!(
            tableau.existential_strategy_type,
            crate::configuration::ExistentialStrategyType::CreationOrder
        );
        assert!(tableau.individual_reuse_strategy.is_none());
    }

    #[test]
    fn final_chance_pass_is_noop_on_an_empty_exact_tableau() {
        // `expand_existentials_final_chance(true)` over a saturated/empty exact
        // tableau makes no change (returns false) — the no-op the default path
        // relies on.
        let mut tableau = Tableau::new();
        assert!(!tableau.expand_existentials_final_chance(true));
        assert!(!tableau.expand_existentials_final_chance(false));
    }

    #[test]
    fn individual_reuse_config_is_honoured() {
        // Selecting IndividualReuse / El installs the reuse strategy object;
        // CreationOrder leaves it None.
        let mut config = Configuration::default();
        config.existential_strategy_type =
            crate::configuration::ExistentialStrategyType::IndividualReuse;
        let tableau = Tableau::with_configuration(&config);
        let reuse = tableau
            .individual_reuse_strategy
            .as_ref()
            .expect("IndividualReuse installs the reuse strategy");
        assert!(!reuse.is_deterministic_strategy(), "INDIVIDUAL_REUSE is non-deterministic");

        config.existential_strategy_type = crate::configuration::ExistentialStrategyType::El;
        let tableau = Tableau::with_configuration(&config);
        let reuse = tableau
            .individual_reuse_strategy
            .as_ref()
            .expect("El installs the reuse strategy");
        assert!(reuse.is_deterministic_strategy(), "EL is deterministic");
    }

    #[test]
    fn validated_blocking_is_inexact_and_drives_the_final_chance_branch() {
        // Installing the validated-blocking validator makes `is_exact()` false,
        // which is what enables `runCalculus`'s final-chance
        // `expandExistentials(true)` branch. On an empty tableau that final-chance
        // pass (the validating `compute_blocking_with(true)` + the expansion walk)
        // runs cleanly and reports no change.
        let mut tableau = Tableau::new();
        assert!(tableau.is_exact());
        let validator = crate::tableau::blocking_validator::BlockingValidator::new(
            &indexmap::IndexSet::new(),
        );
        tableau.set_blocking_validator(validator);
        assert!(!tableau.is_exact(), "validated blocking is inexact");
        assert!(!tableau.expand_existentials_final_chance(true));
    }

    // ---- configure_blocking mirrors Reasoner.createTableau ----
    use crate::configuration::{
        BlockingSignatureCacheType, BlockingStrategyType, DirectBlockingType,
    };
    use crate::tableau::blocking_strategy::{BlockingStrategyKind, DirectBlockingKind};

    fn configured(
        strategy: BlockingStrategyType,
        direct: DirectBlockingType,
        cache: BlockingSignatureCacheType,
        has_inverse: bool,
        has_nominals: bool,
    ) -> Tableau {
        let mut config = Configuration::default();
        config.blocking_strategy_type = strategy;
        config.direct_blocking_type = direct;
        config.blocking_signature_cache_type = cache;
        let mut tableau = Tableau::with_configuration(&config);
        tableau.configure_blocking(&config, has_inverse, has_nominals);
        tableau
    }

    #[test]
    fn optimal_picks_single_without_inverse_pairwise_with_inverse() {
        // OPTIMAL/OPTIMAL, no inverse roles -> SingleDirectBlockingChecker.
        let t = configured(
            BlockingStrategyType::Optimal,
            DirectBlockingType::Optimal,
            BlockingSignatureCacheType::Cached,
            false,
            false,
        );
        assert_eq!(t.blocking_strategy_kind, BlockingStrategyKind::Anywhere);
        assert_eq!(t.direct_blocking_kind, DirectBlockingKind::Single);
        // Cached + no nominals + non-core -> a signature cache exists.
        assert!(t.blocking_signature_cache.is_some());

        // With inverse roles -> PairWiseDirectBlockingChecker.
        let t = configured(
            BlockingStrategyType::Optimal,
            DirectBlockingType::Optimal,
            BlockingSignatureCacheType::Cached,
            true,
            false,
        );
        assert_eq!(t.direct_blocking_kind, DirectBlockingKind::Pairwise);
    }

    #[test]
    fn explicit_direct_blocking_type_overrides_optimal() {
        // SINGLE forces single even with inverse roles.
        let t = configured(
            BlockingStrategyType::Anywhere,
            DirectBlockingType::Single,
            BlockingSignatureCacheType::Cached,
            true,
            false,
        );
        assert_eq!(t.direct_blocking_kind, DirectBlockingKind::Single);
        // PAIR_WISE forces pairwise even without inverse roles.
        let t = configured(
            BlockingStrategyType::Anywhere,
            DirectBlockingType::PairWise,
            BlockingSignatureCacheType::Cached,
            false,
            false,
        );
        assert_eq!(t.direct_blocking_kind, DirectBlockingKind::Pairwise);
    }

    #[test]
    fn ancestor_strategy_is_selected() {
        let t = configured(
            BlockingStrategyType::Ancestor,
            DirectBlockingType::Optimal,
            BlockingSignatureCacheType::Cached,
            false,
            false,
        );
        assert_eq!(t.blocking_strategy_kind, BlockingStrategyKind::Ancestor);
        assert!(t.is_exact(), "ancestor blocking is exact");
    }

    #[test]
    fn core_strategies_select_validated_and_disable_cache() {
        // SIMPLE_CORE -> validated (simple), no signature cache (Java guard).
        let t = configured(
            BlockingStrategyType::SimpleCore,
            DirectBlockingType::Optimal,
            BlockingSignatureCacheType::Cached,
            true,
            false,
        );
        assert_eq!(
            t.blocking_strategy_kind,
            BlockingStrategyKind::ValidatedCore { simple: true }
        );
        assert!(t.blocking_uses_validator());
        assert!(t.blocking_core_is_simple());
        assert!(t.blocking_signature_cache.is_none(), "core disables the cache");

        // COMPLEX_CORE -> validated (complex).
        let t = configured(
            BlockingStrategyType::ComplexCore,
            DirectBlockingType::Optimal,
            BlockingSignatureCacheType::Cached,
            true,
            false,
        );
        assert_eq!(
            t.blocking_strategy_kind,
            BlockingStrategyKind::ValidatedCore { simple: false }
        );
        assert!(t.blocking_uses_validator());
        assert!(!t.blocking_core_is_simple());
    }

    #[test]
    fn nominals_or_not_cached_disable_the_signature_cache() {
        // hasNominals -> no cache even with CACHED (Java's `!hasNominals` guard).
        let t = configured(
            BlockingStrategyType::Anywhere,
            DirectBlockingType::Optimal,
            BlockingSignatureCacheType::Cached,
            false,
            true,
        );
        assert!(t.blocking_signature_cache.is_none());
        // NOT_CACHED -> no cache.
        let t = configured(
            BlockingStrategyType::Anywhere,
            DirectBlockingType::Optimal,
            BlockingSignatureCacheType::NotCached,
            false,
            false,
        );
        assert!(t.blocking_signature_cache.is_none());
    }

    #[test]
    fn default_config_blocking_is_unchanged_for_inverse_role_ontologies() {
        // The historical hard-wired path was pairwise anywhere blocking; with the
        // DEFAULT config that is exactly the selection for an ontology with
        // inverse roles (Optimal -> pairwise, Anywhere strategy, no validator).
        let t = configured(
            BlockingStrategyType::Optimal,
            DirectBlockingType::Optimal,
            BlockingSignatureCacheType::Cached,
            true,
            false,
        );
        assert_eq!(t.blocking_strategy_kind, BlockingStrategyKind::Anywhere);
        assert_eq!(t.direct_blocking_kind, DirectBlockingKind::Pairwise);
        assert!(t.is_exact());
    }

    #[test]
    fn timing_monitor_is_selected_from_configuration() {
        // TIMING installs an answer-neutral monitor.
        let mut config = Configuration::default();
        config.tableau_monitor_type = crate::configuration::TableauMonitorType::Timing;
        let tableau = Tableau::with_configuration(&config);
        assert!(tableau.monitor.is_some(), "TIMING installs a Timer monitor");

        config.tableau_monitor_type =
            crate::configuration::TableauMonitorType::TimingWithPause;
        let tableau = Tableau::with_configuration(&config);
        assert!(tableau.monitor.is_some(), "TIMING_WITH_PAUSE installs a monitor");

        // Debugger monitors are not ported; fall back to no monitor (== NONE).
        config.tableau_monitor_type =
            crate::configuration::TableauMonitorType::DebuggerNoHistory;
        let tableau = Tableau::with_configuration(&config);
        assert!(tableau.monitor.is_none());
    }
}
