// Port of org.semanticweb.HermiT.Configuration.
//
// `Configuration` is HermiT's reasoner-options holder: the choice of blocking
// strategy, existential-expansion strategy, monitor, caching, timeouts and the
// various policy flags, together with the defaults set in HermiT's constructor.
// The OWL-API-specific bits (the `OWLReasonerConfiguration` interface, file
// loading of reuse-strategy concept sets, Java serialization) are represented
// faithfully where they carry semantics and omitted where they are pure Java
// plumbing; the enums and defaults match HermiT exactly.

use std::collections::HashMap;

/// `Configuration.TableauMonitorType`: which (if any) built-in tableau monitor
/// to attach.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TableauMonitorType {
    /// No monitor — the standard setting.
    #[default]
    None,
    /// Periodically prints tableau statistics.
    Timing,
    /// Like `Timing`, but waits for a keystroke at certain points.
    TimingWithPause,
    /// Opens the debugger without recording derivation history.
    DebuggerNoHistory,
    /// Opens the debugger, recording how each fact was derived (memory-heavy).
    DebuggerHistoryOn,
}

/// `Configuration.DirectBlockingType`: the direct-blocking signature to use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DirectBlockingType {
    /// Force single blocking even for ontologies with inverse roles.
    Single,
    /// Force pairwise blocking even when not required.
    PairWise,
    /// Pick the optimal blocking for the ontology.
    #[default]
    Optimal,
}

/// `Configuration.BlockingStrategyType`: which nodes are considered as blockers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BlockingStrategyType {
    /// Anywhere blocking — usually smaller models.
    Anywhere,
    /// Ancestor blocking — usually the largest models.
    Ancestor,
    /// Approximate core blocking validated before termination (complex labels).
    ComplexCore,
    /// Approximate core blocking using only creation-time labels.
    SimpleCore,
    /// `SimpleCore` for nominal ontologies, otherwise `Anywhere`.
    #[default]
    Optimal,
}

/// `Configuration.BlockingSignatureCacheType`: whether blockers are cached.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BlockingSignatureCacheType {
    /// Cache blockers when compatible with the ontology.
    #[default]
    Cached,
    /// Disable caching.
    NotCached,
}

/// `Configuration.ExistentialStrategyType`: how the model is expanded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExistentialStrategyType {
    /// Expand all existentials on the oldest node with unexpanded existentials.
    #[default]
    CreationOrder,
    /// Try to reuse existing individuals before creating fresh successors.
    IndividualReuse,
    /// Deterministic individual reuse for EL ontologies.
    El,
}

impl ExistentialStrategyType {
    /// Mirrors `ExistentialExpansionStrategy.isDeterministic()`: the
    /// `CreationOrderStrategy` is deterministic, and HermiT constructs the EL
    /// `IndividualReuseStrategy(true)` deterministically, while a plain
    /// `IndividualReuseStrategy` is not. Used as a conjunct of
    /// `Tableau.isDeterministic()`.
    pub fn is_deterministic(self) -> bool {
        match self {
            ExistentialStrategyType::CreationOrder | ExistentialStrategyType::El => true,
            ExistentialStrategyType::IndividualReuse => false,
        }
    }
}

/// OWL API `IndividualNodeSetPolicy`: how individual node sets are returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum IndividualNodeSetPolicy {
    #[default]
    ByName,
    BySameAs,
}

/// OWL API `FreshEntityPolicy`: how fresh (unknown) entities are treated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum FreshEntityPolicy {
    #[default]
    Allow,
    Disallow,
}

/// `Configuration.WarningMonitor`: receives warnings (e.g. ignored unsupported
/// datatypes).
pub trait WarningMonitor {
    fn warning(&mut self, warning: &str);
}

/// `Configuration.PrepareReasonerInferences`: which inference tasks to
/// precompute. All default to `true`, as in HermiT.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrepareReasonerInferences {
    pub class_classification_required: bool,
    pub object_property_classification_required: bool,
    pub data_property_classification_required: bool,
    pub object_property_domains_required: bool,
    pub object_property_ranges_required: bool,
    pub realisation_required: bool,
    pub object_property_realisation_required: bool,
    pub data_property_realisation_required: bool,
    pub same_as: bool,
}

impl Default for PrepareReasonerInferences {
    fn default() -> Self {
        PrepareReasonerInferences {
            class_classification_required: true,
            object_property_classification_required: true,
            data_property_classification_required: true,
            object_property_domains_required: true,
            object_property_ranges_required: true,
            realisation_required: true,
            object_property_realisation_required: true,
            data_property_realisation_required: true,
            same_as: true,
        }
    }
}

/// Port of `Configuration`: the reasoner-options holder, with HermiT's default
/// values.
#[derive(Debug, Clone)]
pub struct Configuration {
    pub tableau_monitor_type: TableauMonitorType,
    pub direct_blocking_type: DirectBlockingType,
    pub blocking_strategy_type: BlockingStrategyType,
    pub blocking_signature_cache_type: BlockingSignatureCacheType,
    pub existential_strategy_type: ExistentialStrategyType,
    /// If true, axioms with unsupported datatypes are ignored rather than
    /// raising an error.
    pub ignore_unsupported_datatypes: bool,
    /// Free-form tableau parameters (e.g. the individual-reuse concept sets).
    pub parameters: HashMap<String, String>,
    /// Per-task timeout in milliseconds; `-1` means no timeout.
    pub individual_task_timeout: i64,
    pub individual_node_set_policy: IndividualNodeSetPolicy,
    pub fresh_entity_policy: FreshEntityPolicy,
    /// Enable disjunction-learning (punish factors per disjunct).
    pub use_disjunction_learning: bool,
    /// Buffer add/remove changes until `flush()`.
    pub buffer_changes: bool,
    /// Throw on an inconsistent ontology (vs. returning everything as ⊑ ⊥).
    pub throw_inconsistent_ontology_exception: bool,
    pub prepare_reasoner_inferences: Option<PrepareReasonerInferences>,
    /// Force quasi-order classification even for deterministic ontologies.
    pub force_quasi_order_classification: bool,
}

impl Default for Configuration {
    /// Port of `Configuration()`: HermiT's default settings.
    fn default() -> Self {
        Configuration {
            tableau_monitor_type: TableauMonitorType::None,
            direct_blocking_type: DirectBlockingType::Optimal,
            blocking_strategy_type: BlockingStrategyType::Optimal,
            blocking_signature_cache_type: BlockingSignatureCacheType::Cached,
            existential_strategy_type: ExistentialStrategyType::CreationOrder,
            ignore_unsupported_datatypes: false,
            parameters: HashMap::new(),
            individual_task_timeout: -1,
            individual_node_set_policy: IndividualNodeSetPolicy::ByName,
            fresh_entity_policy: FreshEntityPolicy::Allow,
            use_disjunction_learning: true,
            buffer_changes: true,
            throw_inconsistent_ontology_exception: true,
            prepare_reasoner_inferences: None,
            force_quasi_order_classification: false,
        }
    }
}

impl Configuration {
    pub fn new() -> Configuration {
        Configuration::default()
    }

    /// `getTimeOut`.
    pub fn get_timeout(&self) -> i64 {
        self.individual_task_timeout
    }
    /// `getIndividualNodeSetPolicy`.
    pub fn get_individual_node_set_policy(&self) -> IndividualNodeSetPolicy {
        self.individual_node_set_policy
    }
    /// `getFreshEntityPolicy`.
    pub fn get_fresh_entity_policy(&self) -> FreshEntityPolicy {
        self.fresh_entity_policy
    }

    /// `setIndividualReuseStrategyReuseAlways`: store the always-reuse concept
    /// set under the standard parameter key (one IRI per line).
    pub fn set_individual_reuse_strategy_reuse_always(&mut self, concepts: &[String]) {
        self.parameters
            .insert("IndividualReuseStrategy.reuseAlways".to_string(), concepts.join("\n"));
    }
    /// `setIndividualReuseStrategyReuseNever`.
    pub fn set_individual_reuse_strategy_reuse_never(&mut self, concepts: &[String]) {
        self.parameters
            .insert("IndividualReuseStrategy.reuseNever".to_string(), concepts.join("\n"));
    }

    /// `loadIndividualReuseStrategyReuseAlways`: read IRIs from a file (one per
    /// line, mirroring Java's BufferedReader.readLine) and delegate to the setter.
    pub fn load_individual_reuse_strategy_reuse_always(
        &mut self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<()> {
        let concepts = Self::load_concepts_from_file(path)?;
        self.set_individual_reuse_strategy_reuse_always(&concepts);
        Ok(())
    }

    /// `loadIndividualReuseStrategyReuseNever`: read IRIs from a file and
    /// delegate to the setter.
    pub fn load_individual_reuse_strategy_reuse_never(
        &mut self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<()> {
        let concepts = Self::load_concepts_from_file(path)?;
        self.set_individual_reuse_strategy_reuse_never(&concepts);
        Ok(())
    }

    /// `loadConceptsFromFile`: reads one IRI per line, splitting on \n, \r\n,
    /// or \r (matching Java's BufferedReader.readLine semantics via str::lines).
    fn load_concepts_from_file(
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<Vec<String>> {
        let contents = std::fs::read_to_string(path)?;
        Ok(contents.lines().map(|l| l.to_string()).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defaults_match_hermit() {
        let config = Configuration::default();
        assert_eq!(config.tableau_monitor_type, TableauMonitorType::None);
        assert_eq!(config.direct_blocking_type, DirectBlockingType::Optimal);
        assert_eq!(config.blocking_strategy_type, BlockingStrategyType::Optimal);
        assert_eq!(config.blocking_signature_cache_type, BlockingSignatureCacheType::Cached);
        assert_eq!(config.existential_strategy_type, ExistentialStrategyType::CreationOrder);
        assert!(!config.ignore_unsupported_datatypes);
        assert_eq!(config.individual_task_timeout, -1);
        assert_eq!(config.individual_node_set_policy, IndividualNodeSetPolicy::ByName);
        assert_eq!(config.fresh_entity_policy, FreshEntityPolicy::Allow);
        assert!(config.use_disjunction_learning);
        assert!(config.buffer_changes);
        assert!(config.throw_inconsistent_ontology_exception);
        assert!(config.prepare_reasoner_inferences.is_none());
        assert!(!config.force_quasi_order_classification);
    }

    #[test]
    fn prepare_inferences_default_all_true() {
        let prep = PrepareReasonerInferences::default();
        assert!(prep.class_classification_required);
        assert!(prep.object_property_classification_required);
        assert!(prep.realisation_required);
        assert!(prep.same_as);
    }

    #[test]
    fn reuse_strategy_parameters() {
        let mut config = Configuration::new();
        config.set_individual_reuse_strategy_reuse_always(&["http://example.org/A".to_string()]);
        assert!(config.parameters.contains_key("IndividualReuseStrategy.reuseAlways"));
    }
}
