// Port of the org.semanticweb.HermiT.tableau package: the hypertableau
// reasoning engine -- nodes, extension tables, hyperresolution, merging,
// blocking integration, and the dependency-set infrastructure used for
// dependency-directed backtracking.

pub mod blocking_strategy;
pub mod blocking_validator;
pub mod branching;
pub mod clash_manager;
pub mod datatype_manager;
pub mod dependency_set;
pub mod description_graph_manager;
pub mod dl_clause_evaluator;
pub mod existential_expansion;
pub mod extension_manager;
pub mod extension_table;
pub mod ground_disjunction_header;
pub mod hyperresolution;
pub mod hyperresolution_manager;
pub mod interrupt_flag;
pub mod merging_manager;
pub mod node;
pub mod node_type;
pub mod object;
pub mod reasoning_task_description;
pub mod tuple_index;
pub mod tableau;
pub mod tuple_table;

pub use extension_table::{ExtensionTable, Retrieval, View};
pub use dl_clause_evaluator::DLClauseEvaluator;
pub use hyperresolution_manager::HyperresolutionManager;
pub use node::{Node, NodeId, NodeState};
pub use object::TableauObject;
pub use ground_disjunction_header::GroundDisjunctionHeader;
pub use dependency_set::{
    DependencySet, DependencySetFactory, DependencySetOps, PermanentDependencySet,
    UnionDependencySet,
};
pub use interrupt_flag::{InterruptError, InterruptFlag, InterruptHandle};
pub use node_type::NodeType;
pub use reasoning_task_description::{ReasoningTaskDescription, StandardTestType, TaskArgument};
pub use tuple_index::{TupleIndex, TupleIndexRetrieval};
pub use tableau::Tableau;
pub use tuple_table::TupleTable;
