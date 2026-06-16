// Port of org.semanticweb.HermiT.tableau.NodeType.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NodeType {
    NamedNode,
    NiNode,
    RootConstantNode,
    TreeNode,
    GraphNode,
    ConcreteNode,
}

impl std::fmt::Display for NodeType {
    /// Matches Java `NodeType.toString()` (the enum constant names), used by the
    /// debugger's node listing.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            NodeType::NamedNode => "NAMED_NODE",
            NodeType::NiNode => "NI_NODE",
            NodeType::RootConstantNode => "ROOT_CONSTANT_NODE",
            NodeType::TreeNode => "TREE_NODE",
            NodeType::GraphNode => "GRAPH_NODE",
            NodeType::ConcreteNode => "CONCRETE_NODE",
        };
        f.write_str(name)
    }
}

impl NodeType {
    pub fn get_merge_precedence(self) -> i32 {
        match self {
            NodeType::NamedNode => 0,
            NodeType::NiNode | NodeType::RootConstantNode => 1,
            NodeType::TreeNode | NodeType::GraphNode | NodeType::ConcreteNode => 2,
        }
    }
    pub fn is_ni_target(self) -> bool {
        matches!(self, NodeType::TreeNode | NodeType::GraphNode)
    }
    pub fn is_abstract(self) -> bool {
        matches!(
            self,
            NodeType::NamedNode | NodeType::NiNode | NodeType::TreeNode | NodeType::GraphNode
        )
    }
}
