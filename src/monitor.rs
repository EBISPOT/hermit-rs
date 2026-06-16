// Port of the org.semanticweb.HermiT.monitor package: observers notified of
// tableau events (node creation, clashes, backtracking, datatype checks, ...).
//
// HermiT's `TableauMonitor` is a wide interface (~55 start/finish callbacks);
// `TableauMonitorAdapter` provides no-op defaults, `TableauMonitorFork` fans out
// to two monitors, and `CountingMonitor` accumulates statistics. This port keeps
// the reasoning-relevant lifecycle events as a trait with no-op defaults (the
// adapter), and ports `CountingMonitor`, the fork, `Timer` and `TimerWithPause`.
//
// Monitors are observers with no logical effect; the `Tableau` exposes the
// corresponding events at its hook sites.
//
// Design note (statistics that need tableau state the events do not carry): HermiT's
// `CountingMonitor.isSatisfiableFinished` computes the per-test node count as
// `m_tableau.getNumberOfNodesInTableau()-getNumberOfMergedOrPrunedNodes()` and the
// blocked-node count by iterating the tableau nodes (active && blocked &&
// hasUnprocessedExistentials). The Rust `TableauMonitor` events carry none of
// that state, so the port exposes `record_node_count`/`record_blocked_node`
// hooks for a caller that has the tableau, and otherwise falls back to the
// event-derived live-node count (created - destroyed). Likewise the `Timer`
// statistics block (branching-point level, allocated/created/in-tableau node
// counts, table sizes) comes from a caller-supplied `TableauStatsSnapshot`.
// Wall-clock timings (`m_time`, validation/datatype times) are kept out of the
// answer-neutral monitor and supplied by the caller via the `set_*_time` setters.

use std::time::{Duration, Instant};

/// Port of `TableauMonitor` (the core lifecycle events). All methods default to
/// no-ops, so an empty `impl TableauMonitor for T {}` is `TableauMonitorAdapter`.
pub trait TableauMonitor: std::any::Any {
    /// Upcast to `Any`, so a boxed monitor recovered from the tableau can be
    /// downcast back to its concrete type (e.g. `CountingMonitor`).
    fn as_any(self: Box<Self>) -> Box<dyn std::any::Any>;
    fn is_satisfiable_started(&mut self) {}
    fn is_satisfiable_finished(&mut self, _result: bool) {}
    fn tableau_cleared(&mut self) {}
    fn saturate_started(&mut self) {}
    fn saturate_finished(&mut self, _model_found: bool) {}
    fn iteration_started(&mut self) {}
    fn iteration_finished(&mut self) {}
    fn dl_clause_matched_started(&mut self) {}
    fn dl_clause_matched_finished(&mut self) {}
    fn add_fact_started(&mut self) {}
    fn add_fact_finished(&mut self) {}
    /// `tupleRemoved(tuple)` (ExtensionTable.postRemove). Emitted when a tuple is
    /// removed from an extension table during backtracking/pruning.
    fn tuple_removed(&mut self) {}
    /// `mergeStarted(mergeFrom,mergeInto)` (MergingManager.mergeNodes).
    fn merge_started(&mut self) {}
    /// `mergeFinished(mergeFrom,mergeInto)` (MergingManager.mergeNodes).
    fn merge_finished(&mut self) {}
    /// `nodePruned(node)` (MergingManager.mergeNodes pruning loop).
    fn node_pruned(&mut self) {}
    /// `mergeFactStarted(mergeFrom,mergeInto,sourceTuple,targetTuple)`.
    fn merge_fact_started(&mut self) {}
    /// `mergeFactFinished(mergeFrom,mergeInto,sourceTuple,targetTuple)`.
    fn merge_fact_finished(&mut self) {}
    fn clash_detected(&mut self) {}
    fn backtrack_to_started(&mut self) {}
    fn backtrack_to_finished(&mut self) {}
    fn ground_disjunction_derived(&mut self) {}
    /// `processGroundDisjunctionStarted(groundDisjunction)` (Tableau.java:439).
    fn process_ground_disjunction_started(&mut self) {}
    /// `groundDisjunctionSatisfied(groundDisjunction)` (Tableau.java:460).
    fn ground_disjunction_satisfied(&mut self) {}
    /// `processGroundDisjunctionFinished(groundDisjunction)` (Tableau.java:454).
    fn process_ground_disjunction_finished(&mut self) {}
    /// `disjunctProcessingStarted(groundDisjunction,disjunct)` (Tableau.java:450,
    /// DisjunctionBranchingPoint.java:45). The `disjunct` index is dropped (pure
    /// observer).
    fn disjunct_processing_started(&mut self) {}
    /// `disjunctProcessingFinished(groundDisjunction,disjunct)` (Tableau.java:453,
    /// DisjunctionBranchingPoint.java:59).
    fn disjunct_processing_finished(&mut self) {}
    /// `pushBranchingPointStarted(branchingPoint)` (Tableau.java:513).
    fn push_branching_point_started(&mut self) {}
    /// `pushBranchingPointFinished(branchingPoint)` (Tableau.java:527).
    fn push_branching_point_finished(&mut self) {}
    /// `startNextBranchingPointStarted(branchingPoint)` (Tableau.java:473).
    fn start_next_branching_point_started(&mut self) {}
    /// `startNextBranchingPointFinished(branchingPoint)` (Tableau.java:476).
    fn start_next_branching_point_finished(&mut self) {}
    fn existential_expansion_started(&mut self) {}
    fn existential_expansion_finished(&mut self) {}
    fn existential_satisfied(&mut self) {}
    fn nominal_introduction_started(&mut self) {}
    /// `nominalIntorductionFinished(rootNode,treeNode,annotatedEquality,arg1,arg2)`
    /// (NominalIntroductionManager.java:171). No-op default; args dropped (pure observer).
    fn nominal_introduction_finished(&mut self) {}
    /// `descriptionGraphCheckingStarted(graphIndex1,tupleIndex1,position1,
    /// graphIndex2,tupleIndex2,position2)` (DescriptionGraphManager.java:133).
    /// All six index arguments are dropped (pure observer).
    fn description_graph_checking_started(&mut self) {}
    /// `descriptionGraphCheckingFinished(...)` (DescriptionGraphManager.java:150).
    fn description_graph_checking_finished(&mut self) {}
    fn node_created(&mut self) {}
    fn node_destroyed(&mut self) {}
    /// `unknownDatatypeRestrictionDetectionStarted(dataRange1,node1,dataRange2,
    /// node2)` (DatatypeManager.java:135). Fired when a clash between two unknown
    /// datatype restrictions is detected. Arguments dropped (pure observer).
    fn unknown_datatype_restriction_detection_started(&mut self) {}
    /// `unknownDatatypeRestrictionDetectionFinished(...)` (DatatypeManager.java:138).
    fn unknown_datatype_restriction_detection_finished(&mut self) {}
    fn datatype_checking_started(&mut self) {}
    fn datatype_checking_finished(&mut self) {}
    /// `datatypeConjunctionCheckingStarted(datatypeChecker)`
    /// (DatatypeManager.java:277). Fired around the per-conjunction
    /// satisfiability check. The `DatatypeChecker` argument is dropped (pure
    /// observer).
    fn datatype_conjunction_checking_started(&mut self) {}
    /// `datatypeConjunctionCheckingFinished(datatypeChecker,result)`
    /// (DatatypeManager.java:303). `result` mirrors `!containsClash()` after the
    /// conjunction check.
    fn datatype_conjunction_checking_finished(&mut self, _result: bool) {}
    /// `clashDetectionStarted(tuples...)` (TableauMonitor.java:49). Fired when a
    /// clash is about to be set; the tuple arguments are dropped (pure observer).
    fn clash_detection_started(&mut self) {}
    /// `clashDetectionFinished(tuples...)` (TableauMonitor.java:50).
    fn clash_detection_finished(&mut self) {}
    fn blocking_validation_started(&mut self) {}
    /// `blockingValidationFinished(noInvalidlyBlocked)`. The argument is the number
    /// of invalidly-blocked nodes found during the (first) validation pass; the
    /// Rust port carries it explicitly so `CountingMonitor` can record
    /// `initiallyInvalid`.
    fn blocking_validation_finished(&mut self, _no_invalidly_blocked: u64) {}
    /// `possibleInstanceIsInstance()` — a "possible instance" test that confirmed
    /// the individual is an instance.
    fn possible_instance_is_instance(&mut self) {}
    /// `possibleInstanceIsNotInstance()` — a "possible instance" test that ruled
    /// the individual out.
    fn possible_instance_is_not_instance(&mut self) {}
}

/// `TableauMonitorAdapter`: the all-no-op monitor.
#[derive(Default)]
pub struct TableauMonitorAdapter;
impl TableauMonitor for TableauMonitorAdapter {
    fn as_any(self: Box<Self>) -> Box<dyn std::any::Any> {
        self
    }
}

/// Port of `CountingMonitor.TestRecord`: an immutable record of one satisfiability
/// test — its wall-clock duration (ms), the human-readable task description, and
/// the (flip-corrected) boolean result. Records are `Ord`ered exactly as in Java:
/// descending by time, ties broken by case-insensitive description.
#[derive(Debug, Clone)]
pub struct TestRecord {
    test_time: u64,
    test_description: String,
    test_result: bool,
}

impl TestRecord {
    pub fn new(test_time: u64, test_description: String, test_result: bool) -> TestRecord {
        TestRecord { test_time, test_description, test_result }
    }
    /// `getTestTime`.
    pub fn test_time(&self) -> u64 {
        self.test_time
    }
    /// `getTestDescription`.
    pub fn test_description(&self) -> &str {
        &self.test_description
    }
    /// `getTestResult`.
    pub fn test_result(&self) -> bool {
        self.test_result
    }
}

impl std::fmt::Display for TestRecord {
    /// Mirrors Java's `TestRecord.toString()`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ms", self.test_time)?;
        if self.test_time > 1000 {
            write!(f, " ({})", millis_to_hours_minutes_seconds_string(self.test_time))?;
        }
        write!(f, " for {} (result: {})", self.test_description, self.test_result)
    }
}

impl PartialEq for TestRecord {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}
impl Eq for TestRecord {}
impl PartialOrd for TestRecord {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TestRecord {
    /// Mirrors Java's `compareTo`: descending by time, then case-insensitively
    /// ascending by description.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Long.compare(that.time, this.time) -> descending in this.
        match other.test_time.cmp(&self.test_time) {
            std::cmp::Ordering::Equal => self
                .test_description
                .to_lowercase()
                .cmp(&other.test_description.to_lowercase()),
            ordering => ordering,
        }
    }
}

/// `CountingMonitor.millisToHoursMinutesSecondsString`: format a millisecond
/// duration as `[Xh][Ym][Zs]Wms`.
pub fn millis_to_hours_minutes_seconds_string(millis: u64) -> String {
    let time = millis / 1000;
    // `CountingMonitor` takes the millisecond component from whole seconds
    // (`ms = time % 1000`, where `time = millis / 1000`), not from `millis`.
    let ms = time % 1000;
    let mut s = format!("{:03}ms", ms);
    let secs = time % 60;
    if secs > 0 {
        s = format!("{:02}s{}", secs, s);
    }
    let mins = (time % 3600) / 60;
    if mins > 0 {
        s = format!("{:02}m{}", mins, s);
    }
    let hours = time / 3600;
    if hours > 0 {
        s = format!("{:02}h{}", hours, s);
    }
    s
}

/// Port of `CountingMonitor`: accumulates reasoning statistics, mirroring the
/// Java per-test / overall / average measurement surface plus the `TestRecord`
/// history keyed by message pattern.
///
/// Several Java statistics are read off live tableau state on
/// `isSatisfiableFinished` rather than off monitor events (the exact node count
/// `getNumberOfNodesInTableau()-getNumberOfMergedOrPrunedNodes()`, and the
/// blocked-node count obtained by iterating the tableau nodes). The Rust
/// `TableauMonitor` events do not carry that state, so the port tracks
/// `number_of_nodes`/`number_of_blocked_nodes` from the explicit
/// `record_node_count`/`record_blocked_node` hooks (defaulting to the
/// event-derived live-node count if the caller does not supply one). See the
/// residual note in the module-level docs.
#[derive(Debug, Default, Clone)]
pub struct CountingMonitor {
    test_no: u64,
    // ---- current test (reset on isSatisfiableStarted) ----
    time: u64,
    /// `getNumberOfBacktrackings` — public field (the Java getter equivalent).
    pub number_of_backtrackings: u64,
    /// `getNumberOfNodes` — public field. Set on `isSatisfiableFinished` to the
    /// exact tableau node count if one was pushed via `record_node_count`, else
    /// to the event-derived live-node count (created - destroyed).
    pub number_of_nodes: u64,
    number_of_blocked_nodes: u64,
    /// Current-test clash count (`clashDetected`); folded into the overall total
    /// on `isSatisfiableFinished`.
    pub number_of_clashes: u64,
    test_description: String,
    message_pattern: String,
    test_result: bool,
    /// Most recent (flip-corrected) result, as an `Option` so "no test yet" is
    /// distinguishable. Set on `isSatisfiableFinished`.
    pub last_result: Option<bool>,
    // ---- port-specific event counters (not aggregated by Java's
    // CountingMonitor, but exposed so the finer ExtensionManager/MergingManager
    // events can be observed; downstream tests rely on these public fields) ----
    pub number_of_iterations: u64,
    pub number_of_added_facts: u64,
    pub number_of_tuples_removed: u64,
    pub number_of_merges: u64,
    pub number_of_pruned_nodes: u64,
    pub number_of_merge_facts: u64,
    pub number_of_dl_clauses_matched: u64,
    pub number_of_ground_disjunctions: u64,
    pub number_of_existentials_expanded: u64,
    pub number_of_datatype_checks: u64,
    // validated blocking (current test)
    initial_model_size: u64,
    initially_blocked: u64,
    initially_invalid: u64,
    no_validations: u64,
    validation_time: u64,
    // datatype checking (current test)
    number_datatypes_checked: u64,
    datatype_checking_time: u64,

    // event-derived live-node bookkeeping (fallback for record_node_count)
    created_nodes: u64,
    destroyed_nodes: u64,

    // ---- overall numbers ----
    test_records: std::collections::HashMap<String, Vec<TestRecord>>,
    overall_time: u64,
    overall_number_of_backtrackings: u64,
    overall_number_of_nodes: u64,
    overall_number_of_blocked_nodes: u64,
    overall_number_of_tests: u64,
    overall_number_of_clashes: u64,
    possible_instances_tested: u64,
    possible_instances_instances: u64,
    // validated blocking (overall)
    overall_initial_model_size: u64,
    overall_initially_blocked: u64,
    overall_initially_invalid: u64,
    overall_no_validations: u64,
    overall_validation_time: u64,
    // datatype checking (overall)
    overall_datatype_checking_time: u64,
    overall_number_datatypes_checked: u64,
}

impl CountingMonitor {
    pub fn new() -> CountingMonitor {
        CountingMonitor::default()
    }

    /// `reset`.
    /// Java reset() resets every field except m_testNo, which is the divisor
    /// for all average getters (getAverageTime etc.) and must survive resets.
    pub fn reset(&mut self) {
        let saved_test_no = self.test_no; // Java CountingMonitor.reset():79-112 omits m_testNo
        *self = CountingMonitor::default();
        self.test_no = saved_test_no;
    }

    // --- explicit hooks for tableau-derived per-test state ------------------
    // Java reads these off the live tableau in isSatisfiableFinished; the events
    // do not carry them, so callers that have the tableau push them in.

    /// Supply the exact node count for the current test, mirroring Java's
    /// `m_tableau.getNumberOfNodesInTableau()-getNumberOfMergedOrPrunedNodes()`.
    /// Call before `is_satisfiable_finished`.
    pub fn record_node_count(&mut self, number_of_nodes: u64) {
        self.number_of_nodes = number_of_nodes;
    }
    /// Record one blocked node found while iterating the tableau (a node that is
    /// active, blocked and has unprocessed existentials). Mirrors the increments
    /// of `m_numberOfBlockedNodes` in Java's `isSatisfiableFinished` loop.
    pub fn record_blocked_node(&mut self) {
        self.number_of_blocked_nodes += 1;
    }

    /// `isSatisfiableStarted(reasoningTaskDescription)`. The Rust event has no
    /// arguments, so this overload lets a caller that has the task description
    /// supply the message pattern + description used for the `TestRecord`.
    pub fn is_satisfiable_started_with(&mut self, message_pattern: &str, test_description: &str) {
        self.is_satisfiable_started();
        self.message_pattern = message_pattern.to_string();
        self.test_description = test_description.to_string();
    }
    /// `isSatisfiableFinished(reasoningTaskDescription,result)`. `flip` mirrors
    /// `reasoningTaskDescription.flipSatisfiabilityResult()`.
    pub fn is_satisfiable_finished_with(&mut self, result: bool, flip: bool) {
        let corrected = if flip { !result } else { result };
        self.finish_test(corrected);
    }

    fn finish_test(&mut self, result: bool) {
        self.test_result = result;
        self.last_result = Some(result);
        // `m_time` is wall-clock in Java; the port leaves it at whatever the
        // caller recorded via `set_test_time` (0 by default).
        let record =
            TestRecord::new(self.time, self.test_description.clone(), self.test_result);
        self.test_records.entry(self.message_pattern.clone()).or_default().push(record);
        self.overall_time += self.time;
        self.overall_number_of_backtrackings += self.number_of_backtrackings;
        // If the caller did not push an exact node count, fall back to the
        // event-derived live-node count (created - destroyed).
        if self.number_of_nodes == 0 {
            self.number_of_nodes = self.created_nodes.saturating_sub(self.destroyed_nodes);
        }
        self.overall_number_of_nodes += self.number_of_nodes;
        self.overall_number_of_blocked_nodes += self.number_of_blocked_nodes;
        // Java CountingMonitor has no clashDetected() override and never increments
        // m_overallNumberOfClashes; overall_number_of_clashes intentionally stays 0.
        // (number_of_clashes is a Rust-only per-test observable, not folded in.)
        self.overall_initial_model_size += self.initial_model_size;
        self.overall_initially_blocked += self.initially_blocked;
        self.overall_initially_invalid += self.initially_invalid;
        self.overall_no_validations += self.no_validations;
        self.overall_validation_time += self.validation_time;
        self.overall_datatype_checking_time += self.datatype_checking_time;
        self.overall_number_datatypes_checked += self.number_datatypes_checked;
    }

    /// Set the wall-clock duration (ms) of the current test, mirroring Java's
    /// `m_time=System.currentTimeMillis()-m_problemStartTime`. The port keeps
    /// timing out of the answer-neutral monitor and lets the caller supply it.
    pub fn set_test_time(&mut self, millis: u64) {
        self.time = millis;
    }
    /// Set the validation time (ms) accumulated for the current test.
    pub fn set_validation_time(&mut self, millis: u64) {
        self.validation_time = millis;
    }
    /// Set the datatype-checking time (ms) accumulated for the current test.
    pub fn set_datatype_checking_time(&mut self, millis: u64) {
        self.datatype_checking_time = millis;
    }

    /// The number of live (created minus destroyed) nodes seen via events.
    pub fn number_of_live_nodes(&self) -> u64 {
        self.created_nodes.saturating_sub(self.destroyed_nodes)
    }

    // --- TestRecord history getters ----------------------------------------

    /// `getUsedMessagePatterns`.
    pub fn used_message_patterns(&self) -> Vec<String> {
        self.test_records.keys().cloned().collect()
    }
    /// `getTimeSortedTestRecords(limit)` — across all message patterns.
    pub fn time_sorted_test_records(&mut self, limit: usize) -> Vec<TestRecord> {
        self.time_sorted_test_records_for(limit, None)
    }
    /// `getTimeSortedTestRecords(limit, messagePattern)`. Takes `&mut self` because,
    /// for the single-pattern case, Java sorts the *stored* `m_testRecords` list in
    /// place (`Collections.sort(filteredRecords)` on the aliased list) and returns a
    /// sublist view of it; the all-patterns case sorts a freshly-built list instead.
    pub fn time_sorted_test_records_for(
        &mut self,
        limit: usize,
        message_pattern: Option<&str>,
    ) -> Vec<TestRecord> {
        let mut filtered: Vec<TestRecord> = match message_pattern {
            None => {
                let mut all: Vec<TestRecord> =
                    self.test_records.values().flatten().cloned().collect();
                all.sort();
                all
            }
            Some(pattern) => match self.test_records.get_mut(pattern) {
                Some(records) => {
                    records.sort();
                    records.clone()
                }
                None => Vec::new(),
            },
        };
        let limit = limit.min(filtered.len());
        filtered.truncate(limit);
        filtered
    }

    // --- current-test getters ----------------------------------------------

    /// `getTime`.
    pub fn time(&self) -> u64 {
        self.time
    }
    // `getNumberOfBacktrackings`, `getNumberOfNodes` and `getNumberOfClashes` are
    // exposed as the public fields `number_of_backtrackings`, `number_of_nodes`
    // and `number_of_clashes` (Rust cannot have a field and a same-named method).
    /// `getNumberOfBlockedNodes`.
    pub fn number_of_blocked_nodes(&self) -> u64 {
        self.number_of_blocked_nodes
    }
    /// `getTestDescription`.
    pub fn test_description(&self) -> &str {
        &self.test_description
    }
    /// `getTestResult`.
    pub fn test_result(&self) -> bool {
        self.test_result
    }

    // --- current-test blocking-validation getters --------------------------

    /// `getInitialModelSize`.
    pub fn initial_model_size(&self) -> u64 {
        self.initial_model_size
    }
    /// `getInitiallyBlocked`.
    pub fn initially_blocked(&self) -> u64 {
        self.initially_blocked
    }
    /// `getInitiallyInvalid`.
    pub fn initially_invalid(&self) -> u64 {
        self.initially_invalid
    }
    /// `getNoValidations`.
    pub fn no_validations(&self) -> u64 {
        self.no_validations
    }
    /// `getValidationTime`.
    pub fn validation_time(&self) -> u64 {
        self.validation_time
    }
    /// `getNumberDatatypesChecked`.
    pub fn number_datatypes_checked(&self) -> u64 {
        self.number_datatypes_checked
    }
    /// `getDatatypeCheckingTime`.
    pub fn datatype_checking_time(&self) -> u64 {
        self.datatype_checking_time
    }

    /// During the first validation pass, record one node of the initial model
    /// and (optionally) that it is initially blocked. Mirrors the per-node loop
    /// inside Java's `blockingValidationStarted` (which runs only when
    /// `m_noValidations==1`). Call after `blocking_validation_started`.
    pub fn record_initial_model_node(&mut self, blocked: bool) {
        if self.no_validations == 1 {
            self.initial_model_size += 1;
            if blocked {
                self.initially_blocked += 1;
            }
        }
    }

    // --- overall getters ----------------------------------------------------

    /// `getOverallTime`.
    pub fn overall_time(&self) -> u64 {
        self.overall_time
    }
    /// `getOverallNumberOfBacktrackings`.
    pub fn overall_number_of_backtrackings(&self) -> u64 {
        self.overall_number_of_backtrackings
    }
    /// `getOverallNumberOfNodes`.
    pub fn overall_number_of_nodes(&self) -> u64 {
        self.overall_number_of_nodes
    }
    /// `getOverallNumberOfBlockedNodes`.
    pub fn overall_number_of_blocked_nodes(&self) -> u64 {
        self.overall_number_of_blocked_nodes
    }
    /// `getOverallNumberOfTests`.
    pub fn overall_number_of_tests(&self) -> u64 {
        self.overall_number_of_tests
    }
    /// `getOverallNumberOfTests(messagePattern)`.
    pub fn overall_number_of_tests_for(&self, message_pattern: &str) -> u64 {
        self.test_records.get(message_pattern).map(|r| r.len() as u64).unwrap_or(0)
    }
    /// `getOverallNumberOfClashes`.
    pub fn overall_number_of_clashes(&self) -> u64 {
        self.overall_number_of_clashes
    }
    /// `getNumberOfPossibleInstancesTested`.
    pub fn number_of_possible_instances_tested(&self) -> u64 {
        self.possible_instances_tested
    }
    /// `getNumberOfPossibleInstancesInstances`.
    pub fn number_of_possible_instances_instances(&self) -> u64 {
        self.possible_instances_instances
    }
    /// `getOverallInitialModelSize`.
    pub fn overall_initial_model_size(&self) -> u64 {
        self.overall_initial_model_size
    }
    /// `getOverallInitiallyBlocked`.
    pub fn overall_initially_blocked(&self) -> u64 {
        self.overall_initially_blocked
    }
    /// `getOverallInitiallyInvalid`.
    pub fn overall_initially_invalid(&self) -> u64 {
        self.overall_initially_invalid
    }
    /// `getOverallNoValidations`.
    pub fn overall_no_validations(&self) -> u64 {
        self.overall_no_validations
    }
    /// `getOverallValidationTime`.
    pub fn overall_validation_time(&self) -> u64 {
        self.overall_validation_time
    }
    /// `getOverallNumberDatatypesChecked`.
    pub fn overall_number_datatypes_checked(&self) -> u64 {
        self.overall_number_datatypes_checked
    }
    /// `getOverallDatatypeCheckingTime`.
    pub fn overall_datatype_checking_time(&self) -> u64 {
        self.overall_datatype_checking_time
    }

    // --- average getters ----------------------------------------------------

    /// `getAverageTime`.
    pub fn average_time(&self) -> u64 {
        if self.test_no == 0 {
            0
        } else {
            self.overall_time / self.test_no
        }
    }
    /// `getAverageNumberOfBacktrackings`.
    pub fn average_number_of_backtrackings(&self) -> f64 {
        self.rounded(self.overall_number_of_backtrackings)
    }
    /// `getAverageNumberOfNodes`.
    pub fn average_number_of_nodes(&self) -> f64 {
        self.rounded(self.overall_number_of_nodes)
    }
    /// `getAverageNumberOfBlockedNodes`.
    pub fn average_number_of_blocked_nodes(&self) -> f64 {
        self.rounded(self.overall_number_of_blocked_nodes)
    }
    /// `getAverageNumberOfClashes`.
    pub fn average_number_of_clashes(&self) -> f64 {
        self.rounded(self.overall_number_of_clashes)
    }
    /// `getPossiblesToInstances`.
    pub fn possibles_to_instances(&self) -> f64 {
        if self.possible_instances_tested == 0 {
            0.0
        } else {
            round_ratio(self.possible_instances_instances, self.possible_instances_tested, 2)
        }
    }
    /// `getAverageInitialModelSize`.
    pub fn average_initial_model_size(&self) -> f64 {
        self.rounded(self.overall_initial_model_size)
    }
    /// `getAverageInitiallyBlocked`.
    pub fn average_initially_blocked(&self) -> f64 {
        self.rounded(self.overall_initially_blocked)
    }
    /// `getAverageInitiallyInvalid`.
    pub fn average_initially_invalid(&self) -> f64 {
        self.rounded(self.overall_initially_invalid)
    }
    /// `getAverageNoValidations`.
    pub fn average_no_validations(&self) -> f64 {
        self.rounded(self.overall_no_validations)
    }
    /// `getAverageValidationTime`.
    pub fn average_validation_time(&self) -> u64 {
        if self.test_no == 0 {
            0
        } else {
            self.overall_validation_time / self.test_no
        }
    }
    /// `getAverageNumberDatatypesChecked`.
    pub fn average_number_datatypes_checked(&self) -> u64 {
        if self.test_no == 0 {
            0
        } else {
            self.overall_number_datatypes_checked / self.test_no
        }
    }
    /// `getAverageDatatypeCheckingTime`.
    pub fn average_datatype_checking_time(&self) -> u64 {
        if self.test_no == 0 {
            0
        } else {
            self.overall_datatype_checking_time / self.test_no
        }
    }

    /// `getRounded(nominator, m_testNo)` with the default 2 decimal places; the
    /// `m_testNo==0` short-circuit returns 0.
    fn rounded(&self, nominator: u64) -> f64 {
        if self.test_no == 0 {
            0.0
        } else {
            round_ratio(nominator, self.test_no, 2)
        }
    }
}

/// `CountingMonitor.getRounded`: `(int)(ratio*10^n) / 10^n` — i.e. truncating to
/// `decimals` decimal places, exactly matching Java's integer cast.
fn round_ratio(nominator: u64, denominator: u64, decimals: u32) -> f64 {
    if denominator == 0 {
        return 0.0;
    }
    let number = nominator as f64 / denominator as f64;
    let scale = 10f64.powi(decimals as i32);
    // Java casts to `int` (32-bit), so the scaled value truncates toward zero and
    // saturates at Integer.MAX_VALUE; Rust's `as i32` saturates identically.
    let truncated = (number * scale) as i32;
    truncated as f64 / scale
}

impl TableauMonitor for CountingMonitor {
    fn as_any(self: Box<Self>) -> Box<dyn std::any::Any> {
        self
    }
    fn is_satisfiable_started(&mut self) {
        self.test_no += 1;
        self.overall_number_of_tests += 1;
        // reset the current-test counters
        self.number_of_backtrackings = 0;
        self.number_of_nodes = 0;
        self.number_of_blocked_nodes = 0;
        self.number_of_clashes = 0;
        self.created_nodes = 0;
        self.destroyed_nodes = 0;
        self.initial_model_size = 0;
        self.initially_blocked = 0;
        self.initially_invalid = 0;
        self.no_validations = 0;
        self.validation_time = 0;
        self.datatype_checking_time = 0;
        self.number_datatypes_checked = 0;
    }
    fn is_satisfiable_finished(&mut self, result: bool) {
        // No ReasoningTaskDescription is carried by the bare event, so assume no
        // result flip (callers with the task description use
        // `is_satisfiable_finished_with`).
        self.finish_test(result);
    }
    fn clash_detected(&mut self) {
        self.number_of_clashes += 1;
    }
    fn backtrack_to_finished(&mut self) {
        self.number_of_backtrackings += 1;
    }
    fn node_created(&mut self) {
        self.created_nodes += 1;
    }
    fn node_destroyed(&mut self) {
        self.destroyed_nodes += 1;
    }
    fn datatype_checking_started(&mut self) {
        self.number_datatypes_checked += 1;
        self.number_of_datatype_checks += 1;
    }
    // --- port-specific cumulative event counters (not part of Java's
    // CountingMonitor surface; kept so the finer events stay observable) ---
    fn iteration_finished(&mut self) {
        self.number_of_iterations += 1;
    }
    fn add_fact_finished(&mut self) {
        self.number_of_added_facts += 1;
    }
    fn tuple_removed(&mut self) {
        self.number_of_tuples_removed += 1;
    }
    fn merge_started(&mut self) {
        self.number_of_merges += 1;
    }
    fn node_pruned(&mut self) {
        self.number_of_pruned_nodes += 1;
    }
    fn merge_fact_started(&mut self) {
        self.number_of_merge_facts += 1;
    }
    fn dl_clause_matched_finished(&mut self) {
        self.number_of_dl_clauses_matched += 1;
    }
    fn ground_disjunction_derived(&mut self) {
        self.number_of_ground_disjunctions += 1;
    }
    fn existential_expansion_finished(&mut self) {
        self.number_of_existentials_expanded += 1;
    }
    fn blocking_validation_started(&mut self) {
        self.no_validations += 1;
    }
    fn blocking_validation_finished(&mut self, no_invalidly_blocked: u64) {
        if self.no_validations == 1 {
            self.initially_invalid = no_invalidly_blocked;
        }
    }
    fn possible_instance_is_instance(&mut self) {
        self.possible_instances_tested += 1;
        self.possible_instances_instances += 1;
    }
    fn possible_instance_is_not_instance(&mut self) {
        self.possible_instances_tested += 1;
    }
}

/// Port of `TableauMonitorFork`: forwards every event to two monitors.
pub struct TableauMonitorFork<A, B> {
    pub first: A,
    pub second: B,
}

impl<A: TableauMonitor, B: TableauMonitor> TableauMonitorFork<A, B> {
    pub fn new(first: A, second: B) -> TableauMonitorFork<A, B> {
        TableauMonitorFork { first, second }
    }
}

macro_rules! fork {
    ($($name:ident ( $($arg:ident : $ty:ty),* )),* $(,)?) => {
        impl<A: TableauMonitor, B: TableauMonitor> TableauMonitor for TableauMonitorFork<A, B> {
            fn as_any(self: Box<Self>) -> Box<dyn std::any::Any> {
                self
            }
            $(fn $name(&mut self $(, $arg: $ty)*) {
                self.first.$name($($arg),*);
                self.second.$name($($arg),*);
            })*
        }
    };
}
fork!(
    is_satisfiable_started(),
    is_satisfiable_finished(result: bool),
    tableau_cleared(),
    saturate_started(),
    saturate_finished(model_found: bool),
    iteration_started(),
    iteration_finished(),
    dl_clause_matched_started(),
    dl_clause_matched_finished(),
    add_fact_started(),
    add_fact_finished(),
    tuple_removed(),
    merge_started(),
    merge_finished(),
    node_pruned(),
    merge_fact_started(),
    merge_fact_finished(),
    clash_detected(),
    backtrack_to_started(),
    backtrack_to_finished(),
    ground_disjunction_derived(),
    process_ground_disjunction_started(),
    ground_disjunction_satisfied(),
    process_ground_disjunction_finished(),
    disjunct_processing_started(),
    disjunct_processing_finished(),
    push_branching_point_started(),
    push_branching_point_finished(),
    start_next_branching_point_started(),
    start_next_branching_point_finished(),
    existential_expansion_started(),
    existential_expansion_finished(),
    existential_satisfied(),
    nominal_introduction_started(),
    nominal_introduction_finished(),
    description_graph_checking_started(),
    description_graph_checking_finished(),
    node_created(),
    node_destroyed(),
    unknown_datatype_restriction_detection_started(),
    unknown_datatype_restriction_detection_finished(),
    datatype_checking_started(),
    datatype_checking_finished(),
    datatype_conjunction_checking_started(),
    datatype_conjunction_checking_finished(result: bool),
    clash_detection_started(),
    clash_detection_finished(),
    blocking_validation_started(),
    blocking_validation_finished(no_invalidly_blocked: u64),
    possible_instance_is_instance(),
    possible_instance_is_not_instance(),
);

/// Port of `TableauMonitorForwarder`: wraps a single delegate monitor and
/// forwards every event to it, but only while forwarding is switched on (the
/// `m_forwardingOn` gate). Used to attach/detach a monitor at runtime.
pub struct TableauMonitorForwarder<M> {
    pub target: M,
    forwarding_on: bool,
}

impl<M: TableauMonitor> TableauMonitorForwarder<M> {
    pub fn new(target: M) -> TableauMonitorForwarder<M> {
        TableauMonitorForwarder { target, forwarding_on: false }
    }
    /// `isForwardingOn`.
    pub fn is_forwarding_on(&self) -> bool {
        self.forwarding_on
    }
    /// `setForwardingOn`.
    pub fn set_forwarding_on(&mut self, forwarding_on: bool) {
        self.forwarding_on = forwarding_on;
    }
}

macro_rules! forwarder {
    ($($name:ident ( $($arg:ident : $ty:ty),* )),* $(,)?) => {
        impl<M: TableauMonitor> TableauMonitor for TableauMonitorForwarder<M> {
            fn as_any(self: Box<Self>) -> Box<dyn std::any::Any> {
                self
            }
            $(fn $name(&mut self $(, $arg: $ty)*) {
                if self.forwarding_on {
                    self.target.$name($($arg),*);
                }
            })*
        }
    };
}
forwarder!(
    is_satisfiable_started(),
    is_satisfiable_finished(result: bool),
    tableau_cleared(),
    saturate_started(),
    saturate_finished(model_found: bool),
    iteration_started(),
    iteration_finished(),
    dl_clause_matched_started(),
    dl_clause_matched_finished(),
    add_fact_started(),
    add_fact_finished(),
    tuple_removed(),
    merge_started(),
    merge_finished(),
    node_pruned(),
    merge_fact_started(),
    merge_fact_finished(),
    clash_detected(),
    backtrack_to_started(),
    backtrack_to_finished(),
    ground_disjunction_derived(),
    process_ground_disjunction_started(),
    ground_disjunction_satisfied(),
    process_ground_disjunction_finished(),
    disjunct_processing_started(),
    disjunct_processing_finished(),
    push_branching_point_started(),
    push_branching_point_finished(),
    start_next_branching_point_started(),
    start_next_branching_point_finished(),
    existential_expansion_started(),
    existential_expansion_finished(),
    existential_satisfied(),
    nominal_introduction_started(),
    nominal_introduction_finished(),
    description_graph_checking_started(),
    description_graph_checking_finished(),
    node_created(),
    node_destroyed(),
    unknown_datatype_restriction_detection_started(),
    unknown_datatype_restriction_detection_finished(),
    datatype_checking_started(),
    datatype_checking_finished(),
    datatype_conjunction_checking_started(),
    datatype_conjunction_checking_finished(result: bool),
    clash_detection_started(),
    clash_detection_finished(),
    blocking_validation_started(),
    blocking_validation_finished(no_invalidly_blocked: u64),
    possible_instance_is_instance(),
    possible_instance_is_not_instance(),
);

/// Port of `MemoryConsumptionMonitor`: tracks, per satisfiability test, the
/// in-memory size (in KB) of the binary/ternary extension tables and the
/// dependency-set factory, accumulating current / sum / max so current and
/// average usage can be reported. HermiT reads the sizes off the tableau on
/// `isSatisfiableFinished`; here the caller supplies them via `record_test`
/// (the table sizes are engine-internal values, not JVM heap figures).
#[derive(Debug, Default, Clone)]
pub struct MemoryConsumptionMonitor {
    /// HermiT's `MemoryConsumptionMonitor extends CountingMonitor`, so it is a full
    /// tableau monitor that also accumulates every CountingMonitor statistic. This
    /// embedded monitor receives all forwarded events (the Rust analogue of the
    /// `super` calls); its getters expose the inherited counts.
    pub counting: CountingMonitor,
    binary_table_mem: u64,
    ternary_table_mem: u64,
    dependency_sets_mem: u64,
    sum_binary_table_mem: u64,
    sum_ternary_table_mem: u64,
    sum_dependency_sets_mem: u64,
    max_mem: u64,
    test_number: u64,
}

impl MemoryConsumptionMonitor {
    pub fn new() -> MemoryConsumptionMonitor {
        MemoryConsumptionMonitor::default()
    }
    /// `reset`: `super.reset()` followed by clearing the memory counters.
    pub fn reset(&mut self) {
        self.counting.reset();
        self.binary_table_mem = 0;
        self.ternary_table_mem = 0;
        self.dependency_sets_mem = 0;
        self.sum_binary_table_mem = 0;
        self.sum_ternary_table_mem = 0;
        self.sum_dependency_sets_mem = 0;
        self.max_mem = 0;
        self.test_number = 0;
    }
    /// One `isSatisfiableStarted`/`isSatisfiableFinished` cycle: record the three
    /// table sizes (in KB) for this test and fold them into the running totals.
    pub fn record_test(&mut self, binary_kb: u64, ternary_kb: u64, dependency_kb: u64) {
        self.test_number += 1;
        self.binary_table_mem = binary_kb;
        self.ternary_table_mem = ternary_kb;
        self.dependency_sets_mem = dependency_kb;
        self.sum_binary_table_mem += binary_kb;
        self.sum_ternary_table_mem += ternary_kb;
        self.sum_dependency_sets_mem += dependency_kb;
        let sum = binary_kb + ternary_kb + dependency_kb;
        if sum > self.max_mem {
            self.max_mem = sum;
        }
    }
    pub fn current_tableau_expansion_memory_use(&self) -> u64 {
        self.binary_table_mem + self.ternary_table_mem + self.dependency_sets_mem
    }
    pub fn current_binary_table_size(&self) -> u64 {
        self.binary_table_mem
    }
    pub fn current_ternary_table_size(&self) -> u64 {
        self.ternary_table_mem
    }
    pub fn current_dependency_sets_size(&self) -> u64 {
        self.dependency_sets_mem
    }
    pub fn average_tableau_expansion_memory_use(&self) -> u64 {
        if self.test_number == 0 {
            return 0;
        }
        (self.sum_binary_table_mem + self.sum_ternary_table_mem + self.sum_dependency_sets_mem)
            / self.test_number
    }
    pub fn average_binary_table_size(&self) -> u64 {
        if self.test_number == 0 {
            0
        } else {
            self.sum_binary_table_mem / self.test_number
        }
    }
    pub fn average_ternary_table_size(&self) -> u64 {
        if self.test_number == 0 {
            0
        } else {
            self.sum_ternary_table_mem / self.test_number
        }
    }
    pub fn average_dependency_sets_size(&self) -> u64 {
        if self.test_number == 0 {
            0
        } else {
            self.sum_dependency_sets_mem / self.test_number
        }
    }
    pub fn max_tableau_expansion_memory_use(&self) -> u64 {
        self.max_mem
    }
}

// `MemoryConsumptionMonitor extends CountingMonitor`: it is a full tableau monitor
// that forwards every event to the inherited CountingMonitor behaviour. (The
// memory figures themselves are supplied out-of-band via `record_test`, because
// the Rust monitor events -- unlike Java's -- do not carry the tableau, so the
// table sizes cannot be read inside `isSatisfiableFinished`.)
macro_rules! mem_consumption_forward {
    ($($name:ident ( $($arg:ident : $ty:ty),* )),* $(,)?) => {
        impl TableauMonitor for MemoryConsumptionMonitor {
            fn as_any(self: Box<Self>) -> Box<dyn std::any::Any> {
                self
            }
            $(fn $name(&mut self $(, $arg: $ty)*) {
                self.counting.$name($($arg),*);
            })*
        }
    };
}
mem_consumption_forward!(
    is_satisfiable_started(),
    is_satisfiable_finished(result: bool),
    tableau_cleared(),
    saturate_started(),
    saturate_finished(model_found: bool),
    iteration_started(),
    iteration_finished(),
    dl_clause_matched_started(),
    dl_clause_matched_finished(),
    add_fact_started(),
    add_fact_finished(),
    tuple_removed(),
    merge_started(),
    merge_finished(),
    node_pruned(),
    merge_fact_started(),
    merge_fact_finished(),
    clash_detected(),
    backtrack_to_started(),
    backtrack_to_finished(),
    ground_disjunction_derived(),
    process_ground_disjunction_started(),
    ground_disjunction_satisfied(),
    process_ground_disjunction_finished(),
    disjunct_processing_started(),
    disjunct_processing_finished(),
    push_branching_point_started(),
    push_branching_point_finished(),
    start_next_branching_point_started(),
    start_next_branching_point_finished(),
    existential_expansion_started(),
    existential_expansion_finished(),
    existential_satisfied(),
    nominal_introduction_started(),
    nominal_introduction_finished(),
    description_graph_checking_started(),
    description_graph_checking_finished(),
    node_created(),
    node_destroyed(),
    unknown_datatype_restriction_detection_started(),
    unknown_datatype_restriction_detection_finished(),
    datatype_checking_started(),
    datatype_checking_finished(),
    datatype_conjunction_checking_started(),
    datatype_conjunction_checking_finished(result: bool),
    clash_detection_started(),
    clash_detection_finished(),
    blocking_validation_started(),
    blocking_validation_finished(no_invalidly_blocked: u64),
    possible_instance_is_instance(),
    possible_instance_is_not_instance(),
);

/// A generic elapsed-time stopwatch (the original Rust helper; not the HermiT
/// `Timer` monitor, which is ported below as [`Timer`]). Accumulates wall-clock
/// time across start/stop spans.
#[derive(Default)]
pub struct Stopwatch {
    started: Option<Instant>,
    elapsed: Duration,
}

impl Stopwatch {
    pub fn new() -> Stopwatch {
        Stopwatch::default()
    }
    pub fn start(&mut self) {
        self.started = Some(Instant::now());
    }
    pub fn stop(&mut self) {
        if let Some(started) = self.started.take() {
            self.elapsed += started.elapsed();
        }
    }
    pub fn elapsed(&self) -> Duration {
        self.elapsed
    }
}

/// A snapshot of the tableau figures that HermiT's `Timer.doStatistics` reads off
/// the live tableau (`getCurrentBranchingPointLevel`, `getNumberOfAllocatedNodes`,
/// `getNumberOfNodeCreations`, `getNumberOfNodesInTableau`,
/// `getNumberOfMergedOrPrunedNodes`, and the three table sizes in KB). The Rust
/// `TableauMonitor` events do not carry these, so the caller supplies them when
/// asking the [`Timer`] to print statistics. Everything is `0` by default, which
/// reproduces a faithful (if empty) statistics line.
#[derive(Debug, Default, Clone, Copy)]
pub struct TableauStatsSnapshot {
    pub current_branching_point_level: i64,
    pub allocated_nodes: u64,
    pub node_creations: u64,
    pub nodes_in_tableau: u64,
    pub merged_or_pruned_nodes: u64,
    pub binary_table_kb: u64,
    pub ternary_table_kb: u64,
    pub dependency_set_factory_kb: u64,
}

/// Port of HermiT's `Timer` (`TableauMonitorAdapter`): on `isSatisfiableStarted`
/// it prints the task description and "...", on `isSatisfiableFinished` prints
/// YES/NO and a statistics block, and periodically (every 30s in Java) prints a
/// progress statistics block from `iterationStarted`. It writes to a caller-
/// provided sink rather than `System.out`/`System.err`; the sink choice keeps the
/// answer-neutral monitor free of any global I/O side effects and makes it
/// testable (a `Vec<u8>` in tests). The periodic 30s trigger is parameterised as
/// `status_interval` so tests can drive it deterministically via
/// [`Timer::iteration_started_at`].
///
/// The tableau-derived numbers in the statistics block (branching-point level,
/// node counts, table sizes) are not available from monitor events; the caller
/// supplies them through a [`TableauStatsSnapshot`] set via
/// [`Timer::set_stats_snapshot`] (default: all zeros).
pub struct Timer<W: std::io::Write> {
    output: W,
    problem_start: Option<Instant>,
    last_status: Option<Instant>,
    number_of_backtrackings: u64,
    test_number: u64,
    /// How long between periodic progress reports (Java hard-codes 30s).
    status_interval: Duration,
    snapshot: TableauStatsSnapshot,
}

impl<W: std::io::Write> Timer<W> {
    /// `Timer(PrintWriter)` — build a Timer writing to the given sink.
    pub fn new(output: W) -> Timer<W> {
        Timer {
            output,
            problem_start: None,
            last_status: None,
            number_of_backtrackings: 0,
            test_number: 0,
            status_interval: Duration::from_secs(30),
            snapshot: TableauStatsSnapshot::default(),
        }
    }
    /// Override the periodic-report interval (Java's fixed 30s).
    pub fn set_status_interval(&mut self, interval: Duration) {
        self.status_interval = interval;
    }
    /// Supply the latest tableau figures used by the statistics block.
    pub fn set_stats_snapshot(&mut self, snapshot: TableauStatsSnapshot) {
        self.snapshot = snapshot;
    }
    /// Consume the Timer and return the underlying sink (useful in tests).
    pub fn into_inner(self) -> W {
        self.output
    }
    /// Borrow the underlying sink.
    pub fn output(&self) -> &W {
        &self.output
    }

    /// `Timer.start()`.
    fn start(&mut self) {
        self.number_of_backtrackings = 0;
        let now = Instant::now();
        self.problem_start = Some(now);
        self.last_status = Some(now);
    }

    /// `isSatisfiableStarted` with the task description text (the bare event has
    /// no arguments).
    pub fn is_satisfiable_started_with(&mut self, task_description: &str) {
        let _ = write!(self.output, "{} ...", task_description);
        let _ = self.output.flush();
        self.start();
    }
    /// `isSatisfiableFinished` with the (flip-corrected) result.
    pub fn is_satisfiable_finished_with(&mut self, result: bool, flip: bool) {
        let corrected = if flip { !result } else { result };
        let _ = writeln!(self.output, "{}", if corrected { "YES" } else { "NO" });
        self.do_statistics();
    }

    /// `iterationStarted` keyed off an explicit "now" so tests are deterministic.
    /// Prints a progress statistics block once `status_interval` has elapsed
    /// since the last report.
    pub fn iteration_started_at(&mut self, now: Instant) {
        if let (Some(last), Some(problem_start)) = (self.last_status, self.problem_start) {
            if now.duration_since(last) > self.status_interval {
                if last == problem_start {
                    let _ = writeln!(self.output);
                }
                self.do_statistics();
                // Java re-reads the wall clock AFTER `doStatistics()` to restart the
                // window (`m_lastStatusTime=System.currentTimeMillis()`), so the
                // statistics' own duration is excluded from the next interval.
                self.last_status = Some(Instant::now());
            }
        }
    }

    /// `doStatistics`: writes the multi-line statistics block to the sink.
    fn do_statistics(&mut self) {
        let duration_ms = self
            .problem_start
            .map(|s| s.elapsed().as_millis() as u64)
            .unwrap_or(0);
        let s = &self.snapshot;
        let mut buf = String::new();
        buf.push_str(&format!(
            "    Test:   {:<7}",
            self.test_number
        ));
        buf.push_str(&format!("  Duration:  {:<7}", format!("{} ms", duration_ms)));
        buf.push_str(&format!(
            "   Current branching point: {:<7}",
            s.current_branching_point_level
        ));
        if self.number_of_backtrackings > 0 {
            buf.push_str(&format!("    Backtrackings: {}", self.number_of_backtrackings));
        }
        buf.push('\n');
        buf.push_str(&format!("    Nodes:  allocated:    {:<7}", s.allocated_nodes));
        buf.push_str(&format!("    used: {:<7}", s.node_creations));
        buf.push_str(&format!("    in tableau: {:<7}", s.nodes_in_tableau));
        if s.merged_or_pruned_nodes > 0 {
            buf.push_str(&format!("    merged/pruned: {}", s.merged_or_pruned_nodes));
        }
        buf.push('\n');
        buf.push_str(&format!(
            "    Sizes:  binary table: {:<7}",
            format!("{} kb", s.binary_table_kb)
        ));
        buf.push_str(&format!("    ternary table: {:<7}", format!("{} kb", s.ternary_table_kb)));
        buf.push_str(&format!(
            "    dependency set factory: {:<7}",
            format!("{} kb", s.dependency_set_factory_kb)
        ));
        buf.push('\n');
        buf.push('\n');
        let _ = write!(self.output, "{}", buf);
        let _ = self.output.flush();
    }
}

impl<W: std::io::Write + 'static> TableauMonitor for Timer<W> {
    fn as_any(self: Box<Self>) -> Box<dyn std::any::Any> {
        self
    }
    fn is_satisfiable_started(&mut self) {
        // No task description carried by the bare event.
        self.is_satisfiable_started_with("");
    }
    fn is_satisfiable_finished(&mut self, result: bool) {
        self.is_satisfiable_finished_with(result, false);
    }
    fn iteration_started(&mut self) {
        self.iteration_started_at(Instant::now());
    }
    fn saturate_started(&mut self) {
        self.test_number += 1;
    }
    fn backtrack_to_finished(&mut self) {
        self.number_of_backtrackings += 1;
    }
}

/// Port of `TimerWithPause`: a [`Timer`] that, after each statistics block,
/// prompts "Press something to continue.." and blocks until a line is read from
/// its input source. The Rust port parameterises both the output sink and the
/// input source (Java hard-codes `System.in`); when no interactive input is
/// wanted (e.g. tests), pass an empty reader, which yields EOF immediately and so
/// never blocks. This is an observer and never affects reasoning.
pub struct TimerWithPause<W: std::io::Write, R: std::io::BufRead> {
    timer: Timer<W>,
    input: R,
}

impl<W: std::io::Write, R: std::io::BufRead> TimerWithPause<W, R> {
    pub fn new(output: W, input: R) -> TimerWithPause<W, R> {
        TimerWithPause { timer: Timer::new(output), input }
    }
    /// Access the inner [`Timer`] (e.g. to set the snapshot / interval).
    pub fn timer_mut(&mut self) -> &mut Timer<W> {
        &mut self.timer
    }
    /// Borrow the inner [`Timer`].
    pub fn timer(&self) -> &Timer<W> {
        &self.timer
    }
    pub fn into_inner(self) -> (W, R) {
        (self.timer.output, self.input)
    }

    /// `doStatistics`: delegate to the inner Timer, then prompt and wait for a
    /// line from the input source (EOF returns immediately).
    fn do_statistics(&mut self) {
        self.timer.do_statistics();
        // Java prints the prompt to `System.out` directly (not to `m_output`, which
        // carries the statistics), then blocks on input.
        print!("Press something to continue.. ");
        let _ = std::io::Write::flush(&mut std::io::stdout());
        let mut line = String::new();
        let _ = self.input.read_line(&mut line);
    }

    pub fn is_satisfiable_started_with(&mut self, task_description: &str) {
        self.timer.is_satisfiable_started_with(task_description);
    }
    pub fn is_satisfiable_finished_with(&mut self, result: bool, flip: bool) {
        let corrected = if flip { !result } else { result };
        let _ = writeln!(
            self.timer.output,
            "{}",
            if corrected { "YES" } else { "NO" }
        );
        self.do_statistics();
    }
    pub fn iteration_started_at(&mut self, now: Instant) {
        // Mirror Timer::iteration_started_at but route the periodic report
        // through the pausing doStatistics.
        if let (Some(last), Some(problem_start)) =
            (self.timer.last_status, self.timer.problem_start)
        {
            if now.duration_since(last) > self.timer.status_interval {
                if last == problem_start {
                    let _ = writeln!(self.timer.output);
                }
                self.do_statistics();
                // `TimerWithPause.doStatistics` blocks on input; Java re-reads the
                // clock afterwards so the 30s window restarts from AFTER the pause.
                self.timer.last_status = Some(Instant::now());
            }
        }
    }
}

impl<W: std::io::Write + 'static, R: std::io::BufRead + 'static> TableauMonitor
    for TimerWithPause<W, R>
{
    fn as_any(self: Box<Self>) -> Box<dyn std::any::Any> {
        self
    }
    fn is_satisfiable_started(&mut self) {
        self.is_satisfiable_started_with("");
    }
    fn is_satisfiable_finished(&mut self, result: bool) {
        self.is_satisfiable_finished_with(result, false);
    }
    fn iteration_started(&mut self) {
        self.iteration_started_at(Instant::now());
    }
    fn saturate_started(&mut self) {
        self.timer.test_number += 1;
    }
    fn backtrack_to_finished(&mut self) {
        self.timer.number_of_backtrackings += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counting_monitor_accumulates() {
        let mut counter = CountingMonitor::new();
        counter.is_satisfiable_started();
        counter.node_created();
        counter.node_created();
        counter.node_created();
        counter.node_destroyed();
        counter.clash_detected();
        counter.backtrack_to_finished();
        counter.is_satisfiable_finished(true);
        // 3 created - 1 destroyed = 2 live nodes (used as the node count since no
        // exact count was pushed).
        assert_eq!(counter.number_of_nodes, 2);
        assert_eq!(counter.number_of_live_nodes(), 2);
        assert_eq!(counter.number_of_clashes, 1);
        assert_eq!(counter.number_of_backtrackings, 1);
        assert_eq!(counter.last_result, Some(true));
        assert!(counter.test_result());
    }

    #[test]
    fn counting_monitor_full_statistics_surface() {
        let mut c = CountingMonitor::new();
        // ---- test 1: a SAT test with backtracking, clashes, datatype + validation
        c.is_satisfiable_started_with("pattern.A", "is A satisfiable");
        c.node_created();
        c.node_created();
        c.backtrack_to_finished();
        c.clash_detected();
        c.clash_detected();
        c.datatype_checking_started(); // counts a datatype check
        c.datatype_checking_finished();
        c.set_datatype_checking_time(7);
        // first validation pass: 3-node initial model, 1 of them blocked
        c.blocking_validation_started();
        c.record_initial_model_node(false);
        c.record_initial_model_node(true);
        c.record_initial_model_node(false);
        c.blocking_validation_finished(2); // 2 invalidly blocked
        c.set_validation_time(11);
        c.set_test_time(100);
        c.record_node_count(2);
        c.is_satisfiable_finished_with(true, false);

        // current-test getters reflect test 1
        assert_eq!(c.number_of_backtrackings, 1);
        assert_eq!(c.number_of_nodes, 2);
        assert_eq!(c.number_of_clashes, 2);
        assert_eq!(c.number_datatypes_checked(), 1);
        assert_eq!(c.datatype_checking_time(), 7);
        assert_eq!(c.initial_model_size(), 3);
        assert_eq!(c.initially_blocked(), 1);
        assert_eq!(c.initially_invalid(), 2);
        assert_eq!(c.no_validations(), 1);
        assert_eq!(c.validation_time(), 11);
        assert_eq!(c.test_description(), "is A satisfiable");
        assert!(c.test_result());

        // ---- test 2: an UNSAT test (flipped result), no validation/datatype
        c.is_satisfiable_started_with("pattern.B", "is B satisfiable");
        c.node_created();
        c.backtrack_to_finished();
        c.backtrack_to_finished();
        c.clash_detected();
        c.set_test_time(40);
        c.record_node_count(1);
        c.is_satisfiable_finished_with(true, true); // flip -> false

        assert!(!c.test_result());

        // ---- overall aggregates over the two tests
        assert_eq!(c.overall_number_of_tests(), 2);
        assert_eq!(c.overall_number_of_backtrackings(), 3); // 1 + 2
        assert_eq!(c.overall_number_of_nodes(), 3); // 2 + 1
        // Java CountingMonitor never increments m_overallNumberOfClashes (no
        // clashDetected() override), so overall_number_of_clashes is always 0.
        assert_eq!(c.overall_number_of_clashes(), 0);
        assert_eq!(c.overall_number_of_blocked_nodes(), 0);
        assert_eq!(c.overall_time(), 140); // 100 + 40
        assert_eq!(c.overall_initial_model_size(), 3);
        assert_eq!(c.overall_initially_blocked(), 1);
        assert_eq!(c.overall_initially_invalid(), 2);
        assert_eq!(c.overall_no_validations(), 1);
        assert_eq!(c.overall_validation_time(), 11);
        assert_eq!(c.overall_number_datatypes_checked(), 1);
        assert_eq!(c.overall_datatype_checking_time(), 7);

        // averages (test_no == 2)
        assert_eq!(c.average_time(), 70); // 140/2
        assert_eq!(c.average_number_of_backtrackings(), 1.5); // 3/2
        assert_eq!(c.average_number_of_nodes(), 1.5);
        // Java CountingMonitor never increments m_overallNumberOfClashes (no
        // clashDetected override), so the average is getRounded(0, testNo) = 0.0.
        assert_eq!(c.average_number_of_clashes(), 0.0);
        assert_eq!(c.average_validation_time(), 5); // 11/2 truncated
        assert_eq!(c.average_datatype_checking_time(), 3); // 7/2 truncated

        // per-pattern test counts and message patterns
        assert_eq!(c.overall_number_of_tests_for("pattern.A"), 1);
        assert_eq!(c.overall_number_of_tests_for("pattern.B"), 1);
        assert_eq!(c.overall_number_of_tests_for("pattern.C"), 0);
        let mut patterns = c.used_message_patterns();
        patterns.sort();
        assert_eq!(patterns, vec!["pattern.A".to_string(), "pattern.B".to_string()]);

        // possible-instance counters
        c.possible_instance_is_instance();
        c.possible_instance_is_instance();
        c.possible_instance_is_not_instance();
        assert_eq!(c.number_of_possible_instances_tested(), 3);
        assert_eq!(c.number_of_possible_instances_instances(), 2);
        // 2/3 truncated to 2 decimal places == 0.66
        assert_eq!(c.possibles_to_instances(), 0.66);

        // reset clears everything
        c.reset();
        assert_eq!(c.overall_number_of_tests(), 0);
        assert_eq!(c.overall_time(), 0);
        assert!(c.used_message_patterns().is_empty());
        assert_eq!(c.average_time(), 0);
    }

    #[test]
    fn counting_monitor_test_record_history_is_time_sorted() {
        let mut c = CountingMonitor::new();
        // three tests under one pattern with different durations
        for (desc, ms) in [("fast", 10u64), ("slow", 300u64), ("medium", 100u64)] {
            c.is_satisfiable_started_with("p", desc);
            c.set_test_time(ms);
            c.record_node_count(1);
            c.is_satisfiable_finished_with(true, false);
        }
        // getTimeSortedTestRecords sorts descending by time
        let top2 = c.time_sorted_test_records(2);
        assert_eq!(top2.len(), 2);
        assert_eq!(top2[0].test_time(), 300);
        assert_eq!(top2[0].test_description(), "slow");
        assert_eq!(top2[1].test_time(), 100);
        // limit larger than size clamps
        assert_eq!(c.time_sorted_test_records(99).len(), 3);
        // filtered by an unknown pattern -> empty
        assert!(c.time_sorted_test_records_for(10, Some("other")).is_empty());
        // TestRecord Display
        let record = &top2[0];
        assert!(record.to_string().contains("for slow"));
        assert!(record.to_string().contains("result: true"));
    }

    #[test]
    fn millis_to_hms_formatting() {
        // The millisecond field is derived from whole seconds (`(millis/1000)%1000`),
        // matching `CountingMonitor.millisToHoursMinutesSecondsString`.
        assert_eq!(millis_to_hours_minutes_seconds_string(7), "000ms");
        assert_eq!(millis_to_hours_minutes_seconds_string(1500), "01s001ms");
        assert_eq!(
            millis_to_hours_minutes_seconds_string(3_661_000),
            "01h01m01s661ms"
        );
    }

    #[test]
    fn fork_and_forwarder_forward_finer_datatype_events() {
        // A minimal recorder that counts the finer datatype monitor events.
        #[derive(Default)]
        struct Recorder {
            conj_started: u64,
            conj_finished_sat: u64,
            clash_started: u64,
            clash_finished: u64,
        }
        impl TableauMonitor for Recorder {
            fn as_any(self: Box<Self>) -> Box<dyn std::any::Any> {
                self
            }
            fn datatype_conjunction_checking_started(&mut self) {
                self.conj_started += 1;
            }
            fn datatype_conjunction_checking_finished(&mut self, result: bool) {
                if result {
                    self.conj_finished_sat += 1;
                }
            }
            fn clash_detection_started(&mut self) {
                self.clash_started += 1;
            }
            fn clash_detection_finished(&mut self) {
                self.clash_finished += 1;
            }
        }

        // Fork: both delegates see every event.
        let mut fork = TableauMonitorFork::new(Recorder::default(), Recorder::default());
        fork.datatype_conjunction_checking_started();
        fork.datatype_conjunction_checking_finished(true);
        fork.clash_detection_started();
        fork.clash_detection_finished();
        for r in [&fork.first, &fork.second] {
            assert_eq!(r.conj_started, 1);
            assert_eq!(r.conj_finished_sat, 1);
            assert_eq!(r.clash_started, 1);
            assert_eq!(r.clash_finished, 1);
        }

        // Forwarder: gated on the switch.
        let mut fwd = TableauMonitorForwarder::new(Recorder::default());
        fwd.datatype_conjunction_checking_started(); // off -> dropped
        fwd.set_forwarding_on(true);
        fwd.datatype_conjunction_checking_started();
        fwd.datatype_conjunction_checking_finished(false); // not SAT -> not counted
        fwd.clash_detection_started();
        fwd.clash_detection_finished();
        assert_eq!(fwd.target.conj_started, 1);
        assert_eq!(fwd.target.conj_finished_sat, 0);
        assert_eq!(fwd.target.clash_started, 1);
        assert_eq!(fwd.target.clash_finished, 1);
    }

    #[test]
    fn fork_forwards_to_both() {
        let mut fork = TableauMonitorFork::new(CountingMonitor::new(), CountingMonitor::new());
        fork.is_satisfiable_started();
        fork.node_created();
        fork.node_created();
        fork.clash_detected();
        assert_eq!(fork.first.number_of_live_nodes(), 2);
        assert_eq!(fork.second.number_of_live_nodes(), 2);
        assert_eq!(fork.second.number_of_clashes, 1);
    }

    #[test]
    fn forwarder_gates_on_the_switch() {
        let mut forwarder = TableauMonitorForwarder::new(CountingMonitor::new());
        forwarder.set_forwarding_on(true);
        forwarder.is_satisfiable_started();
        forwarder.set_forwarding_on(false);
        // Off: events are dropped.
        forwarder.node_created();
        assert_eq!(forwarder.target.number_of_live_nodes(), 0);
        assert!(!forwarder.is_forwarding_on());

        // Switched on: events reach the delegate.
        forwarder.set_forwarding_on(true);
        forwarder.node_created();
        forwarder.node_created();
        forwarder.clash_detected();
        assert_eq!(forwarder.target.number_of_live_nodes(), 2);
        assert_eq!(forwarder.target.number_of_clashes, 1);

        // Switched back off: further events are dropped again.
        forwarder.set_forwarding_on(false);
        forwarder.node_created();
        assert_eq!(forwarder.target.number_of_live_nodes(), 2);
    }

    #[test]
    fn timer_monitor_writes_yes_no_and_statistics() {
        let mut timer = Timer::new(Vec::<u8>::new());
        timer.set_stats_snapshot(TableauStatsSnapshot {
            current_branching_point_level: 3,
            allocated_nodes: 5,
            node_creations: 4,
            nodes_in_tableau: 4,
            merged_or_pruned_nodes: 1,
            binary_table_kb: 8,
            ternary_table_kb: 2,
            dependency_set_factory_kb: 1,
            ..Default::default()
        });
        timer.saturate_started(); // test number -> 1
        timer.is_satisfiable_started(); // prints "... "
        timer.backtrack_to_finished();
        timer.is_satisfiable_finished(false); // prints "NO" + stats
        let out = String::from_utf8(timer.into_inner()).unwrap();
        assert!(out.contains("NO"));
        assert!(out.contains("Test:"));
        assert!(out.contains("Backtrackings: 1"));
        assert!(out.contains("binary table: 8 kb"));
        assert!(out.contains("merged/pruned: 1"));
    }

    #[test]
    fn timer_periodic_report_fires_after_interval() {
        let mut timer = Timer::new(Vec::<u8>::new());
        timer.set_status_interval(Duration::from_millis(0));
        timer.is_satisfiable_started_with("task X");
        // With a zero interval, any positive elapsed time triggers a report.
        let later = Instant::now() + Duration::from_millis(1);
        timer.iteration_started_at(later);
        let out = String::from_utf8(timer.into_inner()).unwrap();
        assert!(out.contains("task X ..."));
        assert!(out.contains("Nodes:"));
    }

    #[test]
    fn timer_with_pause_drives_without_blocking_on_empty_input() {
        // Empty reader -> read_line returns Ok(0) (EOF) immediately, no block.
        let input = std::io::Cursor::new(Vec::<u8>::new());
        let mut timer = TimerWithPause::new(Vec::<u8>::new(), input);
        timer.timer_mut().set_stats_snapshot(TableauStatsSnapshot::default());
        timer.saturate_started();
        timer.is_satisfiable_started();
        timer.backtrack_to_finished();
        timer.is_satisfiable_finished(true);
        let (out, _) = timer.into_inner();
        let out = String::from_utf8(out).unwrap();
        // The YES/statistics block goes to the output sink; the "Press something"
        // prompt goes to stdout (Java's System.out), so it is NOT in the sink.
        assert!(out.contains("YES"));
        assert!(!out.contains("Press something to continue.."));
    }

    #[test]
    fn timer_with_pause_consumes_one_line_per_report() {
        // Reader with a single line; the pause consumes it and continues. The
        // "Press something" prompt goes to stdout (Java's System.out), not the
        // statistics sink, so the sink carries the NO/statistics block instead.
        let input = std::io::Cursor::new(b"\n".to_vec());
        let mut timer = TimerWithPause::new(Vec::<u8>::new(), input);
        timer.is_satisfiable_started();
        timer.is_satisfiable_finished(false);
        let (out, _) = timer.into_inner();
        assert!(String::from_utf8(out).unwrap().contains("NO"));
    }

    #[test]
    fn stopwatch_accumulates_elapsed() {
        let mut sw = Stopwatch::new();
        sw.start();
        sw.stop();
        // Just assert it ran without panicking and produced a finite duration.
        assert!(sw.elapsed() >= Duration::ZERO);
    }

    #[test]
    fn memory_monitor_accumulates_current_average_max() {
        let mut monitor = MemoryConsumptionMonitor::new();
        assert_eq!(monitor.average_tableau_expansion_memory_use(), 0);
        monitor.record_test(10, 20, 5); // sum 35
        assert_eq!(monitor.current_tableau_expansion_memory_use(), 35);
        assert_eq!(monitor.current_binary_table_size(), 10);
        assert_eq!(monitor.max_tableau_expansion_memory_use(), 35);
        monitor.record_test(30, 40, 5); // sum 75 -> new max
        assert_eq!(monitor.current_tableau_expansion_memory_use(), 75);
        assert_eq!(monitor.max_tableau_expansion_memory_use(), 75);
        // Averages over the two tests: binary (10+30)/2 = 20, total (35+75)/2 = 55.
        assert_eq!(monitor.average_binary_table_size(), 20);
        assert_eq!(monitor.average_tableau_expansion_memory_use(), 55);
        monitor.reset();
        assert_eq!(monitor.max_tableau_expansion_memory_use(), 0);
        assert_eq!(monitor.average_tableau_expansion_memory_use(), 0);
    }
}
