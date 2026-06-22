// Port of org.semanticweb.HermiT.hierarchy.{HierarchyNode, Hierarchy,
// DeterministicClassification}.
//
// A `Hierarchy<E>` is the transitive reduction of a quasi-order over elements
// `E` (e.g. atomic concepts ordered by subsumption): each node groups a set of
// mutually equivalent elements, with parent/child edges to the immediately more
// general / more specific nodes, plus distinguished top and bottom nodes.
//
// `DeterministicClassification::build_hierarchy` turns a "subsumer graph" (each
// element mapped to the set of elements subsuming it) into such a hierarchy by
// computing strongly connected components (Tarjan, identifying equivalent
// elements) in topological order and then transitively reducing the SCC DAG.
// This is a direct port of HermiT's `buildHierarchy`/`visit`.
//
// Java uses object identity and shared mutable `Set<HierarchyNode>`; we use an
// arena (`nodes: Vec<HierarchyNode<E>>`) with `usize` indices for identity and
// `HashSet<usize>` for the parent/child links.

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

pub type NodeRef = usize;

/// Port of `hierarchy.ClassificationProgressMonitor`: notified as each element
/// is classified (for progress reporting).
///
/// Java's interface is exactly `void elementClassified(AtomicConcept element)`
/// — a single callback per element, with no count arguments (HermiT's callers,
/// e.g. `Reasoner`, keep their own running counter and total). The element type
/// is generic here (`&E`) so the monitor serves the concept, object-property
/// and data-property classifications, just as the Java interface is reused for
/// roles (after they are mapped to concepts).
pub trait ClassificationProgressMonitor<E> {
    /// `ClassificationProgressMonitor.elementClassified`: invoked once as
    /// `element` is classified.
    fn element_classified(&mut self, element: &E);

    /// owlmake extension (no Java counterpart): coarse progress through the
    /// *expensive* classification phase — `done` of `total` concepts settled so
    /// far. Fired from the per-concept model-build loops (the deterministic
    /// classifier and the quasi-order leaf-node strategy / possible-subsumer
    /// resolution), which is where a large-ontology classification actually
    /// spends its time — unlike `element_classified`, which only fires during
    /// the cheap final hierarchy build. Default no-op, so it is answer-neutral
    /// and existing monitors are unaffected.
    fn classification_progress(&mut self, _done: usize, _total: usize) {}

    /// owlmake extension (no Java counterpart): announce the current phase of
    /// classification by a short label — `clausify`, `compile`, `consistency`,
    /// `classify` — so a progress display can show what the otherwise-silent
    /// setup steps (which on a large ontology dominate the wall-clock time) are
    /// doing before the per-concept `classification_progress` bar starts.
    /// Default no-op.
    fn classification_phase(&mut self, _phase: &str) {}
}

/// A no-op progress monitor (the default when a caller passes none).
pub struct NoProgressMonitor;
impl<E> ClassificationProgressMonitor<E> for NoProgressMonitor {
    fn element_classified(&mut self, _element: &E) {}
}

#[derive(Clone, Debug)]
pub struct HierarchyNode<E> {
    representative: E,
    equivalent_elements: HashSet<E>,
    parents: HashSet<NodeRef>,
    children: HashSet<NodeRef>,
}

impl<E: Eq + Hash + Clone> HierarchyNode<E> {
    fn new(representative: E) -> HierarchyNode<E> {
        let mut equivalent_elements = HashSet::new();
        equivalent_elements.insert(representative.clone());
        HierarchyNode {
            representative,
            equivalent_elements,
            parents: HashSet::new(),
            children: HashSet::new(),
        }
    }

    pub fn representative(&self) -> &E {
        &self.representative
    }
    pub fn equivalent_elements(&self) -> &HashSet<E> {
        &self.equivalent_elements
    }
    pub fn is_equivalent_element(&self, element: &E) -> bool {
        self.equivalent_elements.contains(element)
    }
    pub fn parent_nodes(&self) -> &HashSet<NodeRef> {
        &self.parents
    }
    pub fn child_nodes(&self) -> &HashSet<NodeRef> {
        &self.children
    }
}

pub struct Hierarchy<E> {
    nodes: Vec<HierarchyNode<E>>,
    top: NodeRef,
    bottom: NodeRef,
    nodes_by_elements: HashMap<E, NodeRef>,
}

impl<E: Eq + Hash + Clone> Hierarchy<E> {
    pub fn node(&self, node: NodeRef) -> &HierarchyNode<E> {
        &self.nodes[node]
    }
    pub fn top_node(&self) -> NodeRef {
        self.top
    }
    pub fn bottom_node(&self) -> NodeRef {
        self.bottom
    }
    pub fn node_for_element(&self, element: &E) -> Option<NodeRef> {
        self.nodes_by_elements.get(element).copied()
    }
    pub fn all_elements(&self) -> impl Iterator<Item = &E> {
        self.nodes_by_elements.keys()
    }
    /// The set of distinct hierarchy nodes.
    pub fn all_nodes(&self) -> HashSet<NodeRef> {
        self.nodes_by_elements.values().copied().collect()
    }
    /// `Hierarchy.isEmpty`: exactly the two elements `owl:Thing` and `owl:Nothing`
    /// remain, each in its own singleton node. Mirrors Java exactly
    /// (`m_nodesByElements.size()==2 && topNode.equiv.size()==1 &&
    /// bottomNode.equiv.size()==1`) -- counting *elements*, not distinct nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes_by_elements.len() == 2
            && self.nodes[self.top].equivalent_elements.len() == 1
            && self.nodes[self.bottom].equivalent_elements.len() == 1
    }

    /// The ancestor nodes (reflexive: includes the node itself), following
    /// parent edges — `HierarchyNode.getAncestorNodes`.
    pub fn ancestor_nodes(&self, start: NodeRef) -> HashSet<NodeRef> {
        self.reachable(start, |node| &self.nodes[node].parents)
    }
    /// The descendant nodes (reflexive), following child edges.
    pub fn descendant_nodes(&self, start: NodeRef) -> HashSet<NodeRef> {
        self.reachable(start, |node| &self.nodes[node].children)
    }
    fn reachable<'a, F>(&'a self, start: NodeRef, neighbours: F) -> HashSet<NodeRef>
    where
        F: Fn(NodeRef) -> &'a HashSet<NodeRef>,
    {
        let mut result: HashSet<NodeRef> = HashSet::new();
        let mut to_visit: VecDeque<NodeRef> = VecDeque::new();
        to_visit.push_back(start);
        while let Some(current) = to_visit.pop_front() {
            if result.insert(current) {
                for &next in neighbours(current) {
                    to_visit.push_back(next);
                }
            }
        }
        result
    }

    /// The elements equivalent to `element` (its hierarchy node's members,
    /// including `element` itself).
    ///
    /// For an element absent from the classified hierarchy (a *fresh* class/role
    /// the caller passed that does not occur in the ontology) this mirrors
    /// `Reasoner.getHierarchyNode`'s default fresh-entity behaviour: the synthetic
    /// node has `equivalentElements = {element}`, so the result is `{element}`
    /// (HermiT's `Collections.singleton(atomicConcept)`), not the empty set.
    pub fn equivalent_elements_of(&self, element: &E) -> HashSet<E> {
        match self.node_for_element(element) {
            Some(node) => self.nodes[node].equivalent_elements.clone(),
            None => std::iter::once(element.clone()).collect(),
        }
    }

    /// The sub-elements of `element`: the members of its descendant nodes
    /// (excluding its own node). `direct` restricts to the immediate children.
    pub fn sub_elements(&self, element: &E, direct: bool) -> HashSet<E> {
        self.relatives(element, direct, true)
    }

    /// The super-elements of `element`: the members of its ancestor nodes
    /// (excluding its own node). `direct` restricts to the immediate parents.
    pub fn super_elements(&self, element: &E, direct: bool) -> HashSet<E> {
        self.relatives(element, direct, false)
    }

    fn relatives(&self, element: &E, direct: bool, descend: bool) -> HashSet<E> {
        let node = match self.node_for_element(element) {
            Some(node) => node,
            None => {
                // A fresh element absent from the hierarchy: `Reasoner.getHierarchy
                // Node` synthesizes a node with `parents = {topNode}` and
                // `children = {bottomNode}`. Its (direct or transitive) super-
                // elements are then the top node's members and its sub-elements the
                // bottom node's members. Returning the empty set here would diverge
                // from HermiT's default fresh-entity policy.
                let boundary = if descend { self.bottom_node() } else { self.top_node() };
                return self.nodes[boundary].equivalent_elements.clone();
            }
        };
        let nodes: HashSet<NodeRef> = if direct {
            if descend {
                self.nodes[node].children.clone()
            } else {
                self.nodes[node].parents.clone()
            }
        } else {
            let mut all = if descend {
                self.descendant_nodes(node)
            } else {
                self.ancestor_nodes(node)
            };
            all.remove(&node);
            all
        };
        let mut result: HashSet<E> = HashSet::new();
        for n in nodes {
            for e in &self.nodes[n].equivalent_elements {
                result.insert(e.clone());
            }
        }
        result
    }

    /// Port of `HierarchyPrinterFSS.printAtomicConceptHierarchy` /
    /// `AtomicConceptPrinter.printNode`: renders the hierarchy in OWL functional
    /// syntax. For every node except the bottom one (which `AtomicConceptPrinter`
    /// skips during traversal) this emits, in Java's exact per-axiom layout:
    ///
    /// * `SubClassOf( child super )` — one per parent edge; the child is this
    ///   node's representative, `super` the parent's. The bottom node is never a
    ///   child here (it is not visited), so edges into bottom are skipped, just
    ///   as in Java; edges into the top node ARE emitted (`SubClassOf( X owl:Thing )`),
    ///   matching Java's printer (whereas the *dumper* drops them).
    /// * `EquivalentClasses( m1 m2 ... )` — for any node with more than one
    ///   member.
    /// * `Declaration( Class( X ) )` — for each member that is neither the top
    ///   nor the bottom element (`needsDeclaration`).
    ///
    /// Note the inner-paren spacing (`SubClassOf( a b )`, not `SubClassOf(a b)`):
    /// this is byte-for-byte Java's `m_out.print("SubClassOf( ")` etc.
    ///
    /// After the traversal Java calls `printNode(0, bottomNode, null, true)`
    /// explicitly (HierarchyPrinterFSS.java:93). With `parentNode=null` no
    /// SubClassOf is emitted, but if the bottom node has more than one member
    /// (i.e. some named class collapsed into owl:Nothing) an
    /// `EquivalentClasses( owl:Nothing :Unsat )` line plus
    /// `Declaration( Class( :Unsat ) )` entries are produced for those classes.
    ///
    /// Members of a node are ordered with bottom first, then top, then the rest
    /// by rendered form (HermiT's `AtomicConceptComparator`, where
    /// `owl:Nothing`/`owl:Thing` sort ahead of ordinary names). The whole set of
    /// axiom lines is then sorted for deterministic output — Java instead emits
    /// them in depth-first-traversal order with `2*level`-space indentation and a
    /// `Prefix(...)`/`Ontology(...)` header produced by `startPrinting` against a
    /// `Prefixes` table; that prefix-abbreviation / indentation / header layer is
    /// out of scope for this element-agnostic helper (the `render` closure
    /// stands in for `Prefixes.abbreviateIRI`), so it is intentionally omitted.
    pub fn print_functional_syntax<F>(&self, render: F) -> String
    where
        F: Fn(&E) -> String,
    {
        // Class hierarchy: SubClassOf / EquivalentClasses / Declaration( Class( ... ) ).
        // needsDeclaration mirrors AtomicConceptPrinter.needsDeclaration (not top/bottom).
        let top_repr = render(&self.nodes[self.top].representative);
        let bottom_repr = render(&self.nodes[self.bottom].representative);
        self.print_functional_syntax_with(
            render,
            "SubClassOf",
            "EquivalentClasses",
            "Class",
            |m: &str| m != top_repr && m != bottom_repr,
        )
    }

    /// Keyword-aware variant of [`print_functional_syntax`] used by the role
    /// hierarchy printers (HierarchyPrinterFSS.java:190-261, `RolePrinter`).
    ///
    /// * `sub_keyword` — e.g. `"SubClassOf"` / `"SubObjectPropertyOf"` / `"SubDataPropertyOf"`
    /// * `equivalent_keyword` — e.g. `"EquivalentClasses"` / `"EquivalentObjectProperties"` / `"EquivalentDataProperties"`
    /// * `decl_keyword` — the inner constructor in `Declaration( K( x ) )`, e.g. `"Class"` / `"ObjectProperty"` / `"DataProperty"`
    /// * `needs_declaration` — mirrors `RolePrinter.needsDeclaration` (HierarchyPrinterFSS.java:259-260):
    ///   returns `false` for top/bottom AND for inverse roles (only `AtomicRole` instances are declared).
    pub fn print_functional_syntax_with<F, D>(
        &self,
        render: F,
        sub_keyword: &str,
        equivalent_keyword: &str,
        decl_keyword: &str,
        needs_declaration: D,
    ) -> String
    where
        F: Fn(&E) -> String,
        D: Fn(&str) -> bool,
    {
        let top_repr = render(&self.nodes[self.top].representative);
        let bottom_repr = render(&self.nodes[self.bottom].representative);
        // `AtomicConceptComparator`: bottom (0) < top (1) < others (2 by IRI).
        let sorted_members = |node: NodeRef| -> Vec<String> {
            let mut m: Vec<String> =
                self.nodes[node].equivalent_elements.iter().map(&render).collect();
            let rank = |s: &String| -> u8 {
                if *s == bottom_repr {
                    0
                } else if *s == top_repr {
                    1
                } else {
                    2
                }
            };
            m.sort_by(|a, b| rank(a).cmp(&rank(b)).then_with(|| a.cmp(b)));
            m
        };

        let mut lines: Vec<String> = Vec::new();
        for &node in &self.all_nodes() {
            // `AtomicConceptPrinter.visit` / `RolePrinter.visit` skips the bottom node.
            if node == self.bottom {
                continue;
            }
            let members = sorted_members(node);
            let representative = &members[0];
            // SubClassOf( child super ) / SubObjectPropertyOf( ... ) / SubDataPropertyOf( ... )
            for &parent in &self.nodes[node].parents {
                lines.push(format!(
                    "{sub_keyword}( {} {} )",
                    representative,
                    sorted_members(parent)[0]
                ));
            }
            // EquivalentClasses( m1 m2 ... ) / EquivalentObjectProperties( ... ) / EquivalentDataProperties( ... )
            if members.len() > 1 {
                lines.push(format!("{equivalent_keyword}( {} )", members.join(" ")));
            }
            // Declaration( Class( X ) ) / Declaration( ObjectProperty( X ) ) / Declaration( DataProperty( X ) )
            // RolePrinter.needsDeclaration (HierarchyPrinterFSS.java:259-260): excludes top/bottom
            // AND inverse roles (only AtomicRole instances get a Declaration).
            for member in &members {
                if needs_declaration(member.as_str()) {
                    lines.push(format!("Declaration( {decl_keyword}( {member} ) )"));
                }
            }
        }
        // Java: printNode(0, bottomNode, null, true) after traversal — no SubXxx,
        // but emit EquivalentXxx + Declarations for a multi-member bottom node.
        let bottom_members = sorted_members(self.bottom);
        if bottom_members.len() > 1 {
            lines.push(format!("{equivalent_keyword}( {} )", bottom_members.join(" ")));
        }
        for member in &bottom_members {
            if needs_declaration(member.as_str()) {
                lines.push(format!("Declaration( {decl_keyword}( {member} ) )"));
            }
        }
        lines.sort();
        lines.join("\n")
    }

    /// Port of `HierarchyDumperFSS`: a fuller OWL-functional-syntax dump than
    /// `print_functional_syntax`. Within each node the members are ordered with
    /// bottom first, then top, then the rest by rendered form (mirroring
    /// HermiT's `*Comparator`, where `owl:Nothing`/`owl:Thing` sort ahead of
    /// ordinary names); the first is the representative. Each multi-member node
    /// yields one `<equivalent_keyword>( m1 m2 ... )` axiom, and each child edge
    /// a `<sub_keyword>( child representative )` axiom — skipping edges out of
    /// the top node and edges into the bottom node, exactly as HermiT does.
    ///
    /// `render` produces the FSS term for an element (e.g. `<iri>` for a class,
    /// `ObjectInverseOf( <iri> )` for an inverse role). The same routine serves
    /// the class, object-property and data-property hierarchies by varying the
    /// keywords and `render`. Output lines are sorted for deterministic results.
    pub fn dump_functional_syntax<F>(
        &self,
        equivalent_keyword: &str,
        sub_keyword: &str,
        render: F,
    ) -> String
    where
        F: Fn(&E) -> String,
    {
        // Sort a node's members with bottom < top < (others by rendered form).
        let rank = |element: &E| -> u8 {
            if *element == self.nodes[self.bottom].representative {
                0
            } else if *element == self.nodes[self.top].representative {
                1
            } else {
                2
            }
        };
        let sorted_members = |node: NodeRef| -> Vec<E> {
            let mut members: Vec<E> = self.nodes[node].equivalent_elements.iter().cloned().collect();
            members.sort_by(|a, b| {
                rank(a).cmp(&rank(b)).then_with(|| render(a).cmp(&render(b)))
            });
            members
        };

        let mut lines: Vec<String> = Vec::new();
        for &node in &self.all_nodes() {
            let members = sorted_members(node);
            let representative = render(&members[0]);
            if members.len() > 1 {
                let rendered: Vec<String> = members.iter().map(&render).collect();
                lines.push(format!("{}( {} )", equivalent_keyword, rendered.join(" ")));
            }
            // Edges out of the top node are omitted.
            if node != self.top {
                for &child in &self.nodes[node].children {
                    // Edges into the bottom node are omitted.
                    if child != self.bottom {
                        let child_representative = render(&sorted_members(child)[0]);
                        lines.push(format!(
                            "{}( {} {} )",
                            sub_keyword, child_representative, representative
                        ));
                    }
                }
            }
        }
        lines.sort();
        // HierarchyDumperFSS.java: each axiom line is \n-terminated (println),
        // and m_out.println() at lines 73/110 adds a trailing blank line even
        // for an empty section (matching printDataPropertyHierarchy at line 149).
        let mut out = String::new();
        for line in &lines {
            out.push_str(line);
            out.push('\n');
        }
        out.push('\n'); // trailing blank line (Java's final m_out.println())
        out
    }

    /// Variant of `dump_functional_syntax` used **only** for the data-property
    /// hierarchy, reproducing the byte-for-byte output of Java's
    /// `HierarchyDumperFSS.printDataPropertyHierarchy` (HierarchyDumperFSS.java:112-149).
    ///
    /// Java has a copy-paste bug at line 127 where the non-first
    /// `EquivalentDataProperties` members are emitted as `>iri>` (leading `>`)
    /// instead of `<iri>` (leading `<`).  The two render closures
    /// `render` and `render_equiv_tail` let callers supply the
    /// well-formed and malformed forms independently without changing the
    /// generic helper.
    pub fn dump_functional_syntax_java_data<F, G>(
        &self,
        equivalent_keyword: &str,
        sub_keyword: &str,
        render: F,
        render_equiv_tail: G,
    ) -> String
    where
        F: Fn(&E) -> String,
        G: Fn(&E) -> String,
    {
        // Sort a node's members with bottom < top < (others by rendered form).
        let rank = |element: &E| -> u8 {
            if *element == self.nodes[self.bottom].representative {
                0
            } else if *element == self.nodes[self.top].representative {
                1
            } else {
                2
            }
        };
        let sorted_members = |node: NodeRef| -> Vec<E> {
            let mut members: Vec<E> = self.nodes[node].equivalent_elements.iter().cloned().collect();
            members.sort_by(|a, b| {
                rank(a).cmp(&rank(b)).then_with(|| render(a).cmp(&render(b)))
            });
            members
        };

        let mut lines: Vec<String> = Vec::new();
        for &node in &self.all_nodes() {
            let members = sorted_members(node);
            let representative = render(&members[0]);
            if members.len() > 1 {
                // Java bug (HierarchyDumperFSS.java:127): non-first members use
                // ">iri>" (leading ">") instead of "<iri>" (leading "<").
                let tail: String = members[1..]
                    .iter()
                    .map(|m| format!(" {}", render_equiv_tail(m)))
                    .collect();
                lines.push(format!("{}( {}{} )", equivalent_keyword, representative, tail));
            }
            // Edges out of the top node are omitted.
            if node != self.top {
                for &child in &self.nodes[node].children {
                    // Edges into the bottom node are omitted.
                    if child != self.bottom {
                        let child_representative = render(&sorted_members(child)[0]);
                        lines.push(format!(
                            "{}( {} {} )",
                            sub_keyword, child_representative, representative
                        ));
                    }
                }
            }
        }
        lines.sort();
        // HierarchyDumperFSS.java: each axiom line is \n-terminated (println),
        // and m_out.println() at lines 73/110/149 adds a trailing blank line even
        // for an empty section.
        let mut out = String::new();
        for line in &lines {
            out.push_str(line);
            out.push('\n');
        }
        out.push('\n'); // trailing blank line (Java's final m_out.println())
        out
    }

    /// `Hierarchy.emptyHierarchy`: a single node containing top, bottom and all
    /// elements (used when the ontology is inconsistent).
    pub fn empty_hierarchy(elements: &[E], top_element: E, bottom_element: E) -> Hierarchy<E> {
        let mut node = HierarchyNode::new(top_element.clone());
        node.equivalent_elements.insert(bottom_element.clone());
        for element in elements {
            node.equivalent_elements.insert(element.clone());
        }
        let mut nodes_by_elements = HashMap::new();
        for element in &node.equivalent_elements {
            nodes_by_elements.insert(element.clone(), 0usize);
        }
        Hierarchy { nodes: vec![node], top: 0, bottom: 0, nodes_by_elements }
    }

    /// `Hierarchy.trivialHierarchy`: a hierarchy containing only the top and
    /// bottom elements, each in its own singleton node, with top the parent of
    /// bottom. Any other element queried against this hierarchy is treated as a
    /// fresh entity (parent = top, child = bottom).
    pub fn trivial_hierarchy(top_element: E, bottom_element: E) -> Hierarchy<E> {
        let top_node = HierarchyNode::new(top_element.clone());
        let mut bottom_node = HierarchyNode::new(bottom_element.clone());
        let mut top_node = top_node;
        top_node.children.insert(1);
        bottom_node.parents.insert(0);
        let mut nodes_by_elements = HashMap::new();
        nodes_by_elements.insert(top_element, 0usize);
        nodes_by_elements.insert(bottom_element, 1usize);
        Hierarchy { nodes: vec![top_node, bottom_node], top: 0, bottom: 1, nodes_by_elements }
    }
}

/// `DeterministicClassification.GraphNode` together with its Tarjan SCC state.
struct GraphNode<E> {
    element: E,
    successors: HashSet<E>,
    dfs_index: i64,
    scc_head: Option<usize>,
    topological_order_index: i64,
}

impl<E> GraphNode<E> {
    fn not_visited(&self) -> bool {
        self.dfs_index == -1
    }
    fn is_assigned_to_scc(&self) -> bool {
        self.topological_order_index != -1
    }
}

/// Port of `DeterministicClassification.buildHierarchy`: builds the hierarchy
/// from a subsumer graph (`subsumers[element]` = the elements that subsume it).
pub fn build_hierarchy<E: Eq + Hash + Clone>(
    top_element: E,
    bottom_element: E,
    subsumers: HashMap<E, HashSet<E>>,
) -> Hierarchy<E> {
    build_hierarchy_with_monitor(top_element, bottom_element, subsumers, &mut NoProgressMonitor)
}

/// As `build_hierarchy`, but reporting progress through a
/// [`ClassificationProgressMonitor`].
///
/// In Java, `ClassificationProgressMonitor.elementClassified(element)` is fired
/// once per element inside `DeterministicClassification.classify()` /
/// `QuasiOrderClassification`, as each element's subsumer set is determined —
/// i.e. once for every element that ends up in the subsumer graph, *before*
/// `buildHierarchy` wires up the edges. The Rust port computes the subsumer map
/// in the reasoner and hands it to `build_hierarchy`, so this is the faithful
/// hook: the monitor is notified once per element of `subsumers` (in iteration
/// order), reproducing Java's one-callback-per-classified-element semantics,
/// then the hierarchy is built exactly as before. The classification algorithm
/// and the resulting hierarchy are unchanged.
///
/// Callers in other modules (e.g. `reasoner.rs`) that already drive their own
/// progress can switch their `build_hierarchy(top, bottom, subsumers)` call to
/// `build_hierarchy_with_monitor(top, bottom, subsumers, monitor)` — that is the
/// single-line change needed to surface progress as Java does.
pub fn build_hierarchy_with_monitor<E, M>(
    top_element: E,
    bottom_element: E,
    subsumers: HashMap<E, HashSet<E>>,
    monitor: &mut M,
) -> Hierarchy<E>
where
    E: Eq + Hash + Clone,
    M: ClassificationProgressMonitor<E> + ?Sized,
{
    for element in subsumers.keys() {
        monitor.element_classified(element);
    }
    let builder = HierarchyBuilder::new(top_element, bottom_element, subsumers);
    builder.run()
}

struct HierarchyBuilder<E> {
    top_element: E,
    bottom_element: E,
    graph_nodes: Vec<GraphNode<E>>,
    index_of: HashMap<E, usize>,
    dfs_value: i64,
    stack: Vec<usize>,
    // The hierarchy being built.
    nodes: Vec<HierarchyNode<E>>,
    nodes_by_elements: HashMap<E, NodeRef>,
    top: NodeRef,
    bottom: NodeRef,
    topological_order: Vec<NodeRef>,
}

impl<E: Eq + Hash + Clone> HierarchyBuilder<E> {
    fn new(top_element: E, bottom_element: E, subsumers: HashMap<E, HashSet<E>>) -> Self {
        let mut graph_nodes: Vec<GraphNode<E>> = Vec::new();
        let mut index_of: HashMap<E, usize> = HashMap::new();
        for (element, succ) in subsumers {
            index_of.insert(element.clone(), graph_nodes.len());
            graph_nodes.push(GraphNode {
                element,
                successors: succ,
                dfs_index: -1,
                scc_head: None,
                topological_order_index: -1,
            });
        }
        // Pre-create the top and bottom hierarchy nodes (arena indices 0 and 1).
        let top_node = HierarchyNode::new(top_element.clone());
        let bottom_node = HierarchyNode::new(bottom_element.clone());
        let mut nodes_by_elements: HashMap<E, NodeRef> = HashMap::new();
        for element in &top_node.equivalent_elements {
            nodes_by_elements.insert(element.clone(), 0);
        }
        for element in &bottom_node.equivalent_elements {
            nodes_by_elements.insert(element.clone(), 1);
        }
        HierarchyBuilder {
            top_element,
            bottom_element,
            graph_nodes,
            index_of,
            dfs_value: 0,
            stack: Vec::new(),
            nodes: vec![top_node, bottom_node],
            nodes_by_elements,
            top: 0,
            bottom: 1,
            topological_order: Vec::new(),
        }
    }

    fn run(mut self) -> Hierarchy<E> {
        // Tarjan SCC starting from the bottom element, producing a reverse
        // topological order of SCC hierarchy nodes.
        if let Some(&bottom_graph) = self.index_of.get(&self.bottom_element.clone()) {
            self.visit(bottom_graph);
        }
        // Some graph nodes may be unreachable from bottom; visit them too so the
        // whole graph is classified (mirrors HermiT processing all elements).
        for i in 0..self.graph_nodes.len() {
            if self.graph_nodes[i].not_visited() {
                self.visit(i);
            }
        }

        // Transitive reduction in topological order.
        let mut reachable_from: HashMap<NodeRef, HashSet<NodeRef>> = HashMap::new();
        let topo = self.topological_order.clone();
        for node in topo {
            let mut reachable_from_node: HashSet<NodeRef> = HashSet::new();
            reachable_from_node.insert(node);

            // Collect the successor SCC-nodes of all equivalent elements.
            let mut all_successors: Vec<usize> = Vec::new();
            let equivalent: Vec<E> = self.nodes[node].equivalent_elements.iter().cloned().collect();
            for element in equivalent {
                if let Some(&gidx) = self.index_of.get(&element) {
                    let succ_elements: Vec<E> =
                        self.graph_nodes[gidx].successors.iter().cloned().collect();
                    for successor in succ_elements {
                        if let Some(&succ_gidx) = self.index_of.get(&successor) {
                            all_successors.push(succ_gidx);
                        }
                    }
                }
            }
            // Sort by topological order index (ascending), then walk from the
            // highest down, attaching only not-yet-reachable successors.
            all_successors
                .sort_by_key(|&gidx| self.graph_nodes[gidx].topological_order_index);
            for &succ_gidx in all_successors.iter().rev() {
                let successor_element = self.graph_nodes[succ_gidx].element.clone();
                let successor_node = self.nodes_by_elements[&successor_element];
                if !reachable_from_node.contains(&successor_node) {
                    self.nodes[node].parents.insert(successor_node);
                    self.nodes[successor_node].children.insert(node);
                    reachable_from_node.insert(successor_node);
                    if let Some(set) = reachable_from.get(&successor_node) {
                        for &r in set {
                            reachable_from_node.insert(r);
                        }
                    }
                }
            }
            reachable_from.insert(node, reachable_from_node);
        }

        Hierarchy {
            nodes: self.nodes,
            top: self.top,
            bottom: self.bottom,
            nodes_by_elements: self.nodes_by_elements,
        }
    }

    /// Port of `DeterministicClassification.visit` (Tarjan SCC).
    fn visit(&mut self, graph_node: usize) {
        self.graph_nodes[graph_node].dfs_index = self.dfs_value;
        self.dfs_value += 1;
        self.graph_nodes[graph_node].scc_head = Some(graph_node);
        self.stack.push(graph_node);

        let successors: Vec<E> = self.graph_nodes[graph_node].successors.iter().cloned().collect();
        for successor in successors {
            if let Some(&succ_idx) = self.index_of.get(&successor) {
                if self.graph_nodes[succ_idx].not_visited() {
                    self.visit(succ_idx);
                }
                if !self.graph_nodes[succ_idx].is_assigned_to_scc() {
                    let succ_head = self.graph_nodes[succ_idx].scc_head.unwrap();
                    let node_head = self.graph_nodes[graph_node].scc_head.unwrap();
                    if self.graph_nodes[succ_head].dfs_index
                        < self.graph_nodes[node_head].dfs_index
                    {
                        self.graph_nodes[graph_node].scc_head = Some(succ_head);
                    }
                }
            }
        }

        if self.graph_nodes[graph_node].scc_head == Some(graph_node) {
            let next_topological_order_index = self.topological_order.len();
            let mut equivalent_elements: Vec<E> = Vec::new();
            loop {
                let popped = self.stack.pop().unwrap();
                self.graph_nodes[popped].topological_order_index =
                    next_topological_order_index as i64;
                equivalent_elements.push(self.graph_nodes[popped].element.clone());
                if popped == graph_node {
                    break;
                }
            }
            let contains_top = equivalent_elements.contains(&self.top_element);
            let contains_bottom = equivalent_elements.contains(&self.bottom_element);
            let hierarchy_node = if contains_top {
                self.top
            } else if contains_bottom {
                self.bottom
            } else {
                let node = HierarchyNode::new(self.graph_nodes[graph_node].element.clone());
                self.nodes.push(node);
                self.nodes.len() - 1
            };
            for element in equivalent_elements {
                self.nodes[hierarchy_node].equivalent_elements.insert(element.clone());
                self.nodes_by_elements.insert(element, hierarchy_node);
            }
            self.topological_order.push(hierarchy_node);
        }
    }
}

/// Result of `HierarchySearch.findPosition`: where a fresh element sits in an
/// existing hierarchy. Either it coincides with an existing node (it is
/// equivalent to that node's members) or it slots strictly between a set of
/// parent nodes and a set of child nodes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Position {
    Existing(NodeRef),
    Between { parents: HashSet<NodeRef>, children: HashSet<NodeRef> },
}

impl<E: Eq + Hash + Clone> Hierarchy<E> {
    /// Port of `HierarchySearch.findPosition`: the top-down / bottom-up search
    /// that locates where `element` belongs in this hierarchy, given a subsumption
    /// oracle `does_subsume(parent, child)` (does `parent` subsume `child`?).
    ///
    /// This is the incremental-insertion machinery HermiT uses in
    /// `QuasiOrderClassification`: it tests `element` against only the
    /// representatives it must, reusing the hierarchy's existing edges.
    pub fn find_position<F>(&self, element: &E, does_subsume: F) -> Position
    where
        F: Fn(&E, &E) -> bool,
    {
        let parents = self.find_parents(element, &does_subsume);
        let children = self.find_children(element, &parents, &does_subsume);
        if parents == children {
            // Both are the single node equivalent to `element`.
            debug_assert!(parents.len() == 1 && children.len() == 1);
            Position::Existing(*parents.iter().next().unwrap())
        } else {
            Position::Between { parents, children }
        }
    }

    fn find_parents<F>(&self, element: &E, does_subsume: &F) -> HashSet<NodeRef>
    where
        F: Fn(&E, &E) -> bool,
    {
        search(
            &[self.top],
            None,
            |u| self.nodes[u].children.clone(),
            |u| self.nodes[u].parents.clone(),
            |u| does_subsume(self.nodes[u].representative(), element),
        )
    }

    fn find_children<F>(
        &self,
        element: &E,
        parent_nodes: &HashSet<NodeRef>,
        does_subsume: &F,
    ) -> HashSet<NodeRef>
    where
        F: Fn(&E, &E) -> bool,
    {
        // If there is a unique parent that `element` also subsumes, the element
        // is equivalent to that parent.
        if parent_nodes.len() == 1 {
            let only = *parent_nodes.iter().next().unwrap();
            if does_subsume(element, self.nodes[only].representative()) {
                return parent_nodes.clone();
            }
        }
        // `marked` becomes the common lower cone: the intersection of the
        // descendant sets of all parent nodes.
        let mut parents_iter = parent_nodes.iter().copied();
        let first = parents_iter.next().expect("at least one parent (top)");
        let mut marked: HashSet<NodeRef> = self.descendant_nodes(first);
        for parent in parents_iter {
            let mut freshly_marked: HashSet<NodeRef> = HashSet::new();
            let mut visited: HashSet<NodeRef> = HashSet::new();
            let mut to_process: VecDeque<NodeRef> = VecDeque::new();
            to_process.push_back(parent);
            while let Some(current) = to_process.pop_front() {
                for &child in &self.nodes[current].children {
                    if marked.contains(&child) {
                        freshly_marked.insert(child);
                    } else if visited.insert(child) {
                        to_process.push_back(child);
                    }
                }
            }
            let mut to_process: VecDeque<NodeRef> = freshly_marked.iter().copied().collect();
            while let Some(current) = to_process.pop_front() {
                for &child in &self.nodes[current].children {
                    if freshly_marked.insert(child) {
                        to_process.push_back(child);
                    }
                }
            }
            marked = freshly_marked;
        }
        // The nodes in the common lower cone that sit directly above bottom and
        // are subsumed by `element`.
        let mut above_bottom: HashSet<NodeRef> = HashSet::new();
        for &node in &marked {
            if self.nodes[node].children.contains(&self.bottom)
                && does_subsume(element, self.nodes[node].representative())
            {
                above_bottom.insert(node);
            }
        }
        if above_bottom.is_empty() {
            let mut children = HashSet::new();
            children.insert(self.bottom);
            children
        } else {
            let start: Vec<NodeRef> = above_bottom.into_iter().collect();
            search(
                &start,
                Some(&marked),
                |u| self.nodes[u].parents.clone(),
                |u| self.nodes[u].children.clone(),
                |u| does_subsume(element, self.nodes[u].representative()),
            )
        }
    }
}

/// Port of `HierarchySearch.search`: a generic graph search that returns the
/// "frontier" — the elements satisfying the predicate that have no satisfying
/// successor. `successors`/`predecessors` give the search direction, `true_of`
/// is the (expensive) predicate, memoized through `SearchCache`.
fn search<S, P, T>(
    start: &[NodeRef],
    possibilities: Option<&HashSet<NodeRef>>,
    successors: S,
    predecessors: P,
    true_of: T,
) -> HashSet<NodeRef>
where
    S: Fn(NodeRef) -> HashSet<NodeRef>,
    P: Fn(NodeRef) -> HashSet<NodeRef>,
    T: Fn(NodeRef) -> bool,
{
    let mut positives: HashSet<NodeRef> = HashSet::new();
    let mut negatives: HashSet<NodeRef> = HashSet::new();
    let mut result: HashSet<NodeRef> = HashSet::new();
    let mut visited: HashSet<NodeRef> = start.iter().copied().collect();
    let mut to_process: VecDeque<NodeRef> = start.iter().copied().collect();
    while let Some(current) = to_process.pop_front() {
        let mut found_subordinate = false;
        for sub in successors(current) {
            if cache_true_of(sub, possibilities, &predecessors, &true_of, &mut positives, &mut negatives)
            {
                found_subordinate = true;
                if visited.insert(sub) {
                    to_process.push_back(sub);
                }
            }
        }
        if !found_subordinate {
            result.insert(current);
        }
    }
    result
}

/// Port of `HierarchySearch.SearchCache.trueOf`: an element is "true" only if
/// all of its predecessors are true and the raw predicate holds; results are
/// memoized in `positives`/`negatives`. `possibilities`, when present, bounds
/// the candidate set (anything outside it is immediately false).
fn cache_true_of<P, T>(
    element: NodeRef,
    possibilities: Option<&HashSet<NodeRef>>,
    predecessors: &P,
    true_of: &T,
    positives: &mut HashSet<NodeRef>,
    negatives: &mut HashSet<NodeRef>,
) -> bool
where
    P: Fn(NodeRef) -> HashSet<NodeRef>,
    T: Fn(NodeRef) -> bool,
{
    if positives.contains(&element) {
        return true;
    }
    if negatives.contains(&element)
        || possibilities.map_or(false, |p| !p.contains(&element))
    {
        return false;
    }
    for superordinate in predecessors(element) {
        if !cache_true_of(superordinate, possibilities, predecessors, true_of, positives, negatives) {
            negatives.insert(element);
            return false;
        }
    }
    if true_of(element) {
        positives.insert(element);
        true
    } else {
        negatives.insert(element);
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet as Set;

    #[test]
    fn print_functional_syntax_matches_java_axiom_format() {
        // Build a hierarchy A ⊑ B with the subsumer graph (A:{A,B,top}, B:{B,top}).
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top", ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "A", "B", "bottom"].into_iter().collect());
        subsumers.insert("A", ["A", "B", "top"].into_iter().collect());
        subsumers.insert("B", ["B", "top"].into_iter().collect());
        let hierarchy = build_hierarchy("top", "bottom", subsumers);

        // Render owl:Thing/owl:Nothing as the FSS keywords so member ordering
        // (bottom < top < others) and `needsDeclaration` are exercised.
        let render = |e: &&str| match *e {
            "top" => "owl:Thing".to_string(),
            "bottom" => "owl:Nothing".to_string(),
            other => other.to_string(),
        };
        let fss = hierarchy.print_functional_syntax(render);

        // Byte-for-byte pinned output: inner-paren spacing, sorted lines, edges
        // into the top node kept (`SubClassOf( B owl:Thing )`), edges into the
        // bottom node dropped (no `SubClassOf( owl:Nothing ... )`), and a
        // `Declaration( Class( X ) )` for every non-top/non-bottom member.
        let expected = "\
Declaration( Class( A ) )
Declaration( Class( B ) )
SubClassOf( A B )
SubClassOf( B owl:Thing )";
        assert_eq!(fss, expected, "got:\n{fss}");
    }

    #[test]
    fn print_functional_syntax_emits_equivalent_classes_axiom() {
        // {P, Q} equivalent, both directly under top.
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top", ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "P", "Q", "bottom"].into_iter().collect());
        subsumers.insert("P", ["P", "Q", "top"].into_iter().collect());
        subsumers.insert("Q", ["Q", "P", "top"].into_iter().collect());
        let hierarchy = build_hierarchy("top", "bottom", subsumers);

        let fss = hierarchy.print_functional_syntax(|e: &&str| e.to_string());
        // The collapsed node yields a single EquivalentClasses axiom with both
        // members (sorted), plus a Declaration for each and one SubClassOf to top.
        assert!(fss.contains("EquivalentClasses( P Q )"), "got:\n{fss}");
        assert!(fss.contains("Declaration( Class( P ) )"), "got:\n{fss}");
        assert!(fss.contains("Declaration( Class( Q ) )"), "got:\n{fss}");
        assert!(fss.contains("SubClassOf( P top )"), "got:\n{fss}");
    }

    #[test]
    fn print_functional_syntax_handles_unsatisfiable_class() {
        // U is unsatisfiable: it is subsumed by everything, so it collapses into
        // the bottom node (equivalent to owl:Nothing).
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top", ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "A", "U", "bottom"].into_iter().collect());
        subsumers.insert("A", ["A", "top"].into_iter().collect());
        // U subsumed by A and top; bottom subsumed by U; so U is equivalent to bottom.
        subsumers.insert("U", ["U", "A", "top", "bottom"].into_iter().collect());
        let hierarchy = build_hierarchy("top", "bottom", subsumers);

        // U joined the bottom node.
        let bottom = hierarchy.bottom_node();
        assert_eq!(hierarchy.node_for_element(&"U"), Some(bottom));

        let render = |e: &&str| match *e {
            "top" => "owl:Thing".to_string(),
            "bottom" => "owl:Nothing".to_string(),
            other => other.to_string(),
        };
        let fss = hierarchy.print_functional_syntax(render);
        // Java calls printNode(0, bottomNode, null, true) after traversal
        // (HierarchyPrinterFSS.java:93): the bottom node IS printed when it has
        // more than one member, emitting EquivalentClasses and Declarations for
        // unsatisfiable classes collapsed into owl:Nothing.
        assert!(fss.contains("EquivalentClasses( owl:Nothing U )"), "got:\n{fss}");
        assert!(fss.contains("Declaration( Class( U ) )"), "got:\n{fss}");
        // No SubClassOf for the bottom node (parentNode=null in the explicit call).
        assert!(!fss.contains("SubClassOf( owl:Nothing"), "got:\n{fss}");
        assert!(!fss.contains("SubClassOf( U"), "got:\n{fss}");
        // The satisfiable class A is still declared and placed under top.
        assert!(fss.contains("Declaration( Class( A ) )"), "got:\n{fss}");
        assert!(fss.contains("SubClassOf( A owl:Thing )"), "got:\n{fss}");
    }

    #[test]
    fn progress_monitor_receives_one_call_per_classified_element() {
        // Build a hierarchy A ⊑ B; the monitor must see exactly one
        // elementClassified per element of the subsumer graph.
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top", ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "A", "B", "bottom"].into_iter().collect());
        subsumers.insert("A", ["A", "B", "top"].into_iter().collect());
        subsumers.insert("B", ["B", "top"].into_iter().collect());
        let total = subsumers.len();

        // A monitor matching Java's `elementClassified(AtomicConcept element)`:
        // it records each classified element.
        struct Recorder {
            classified: Vec<String>,
        }
        impl ClassificationProgressMonitor<&str> for Recorder {
            fn element_classified(&mut self, element: &&str) {
                self.classified.push((*element).to_string());
            }
        }
        let mut recorder = Recorder { classified: Vec::new() };
        let hierarchy =
            build_hierarchy_with_monitor("top", "bottom", subsumers, &mut recorder);

        // One callback per element, covering exactly the subsumer-graph elements.
        assert_eq!(recorder.classified.len(), total);
        let seen: Set<&str> = recorder.classified.iter().map(|s| s.as_str()).collect();
        assert_eq!(
            seen,
            ["top", "bottom", "A", "B"].into_iter().collect::<Set<_>>()
        );

        // The monitored build produces the same hierarchy as the plain build.
        assert!(hierarchy
            .print_functional_syntax(|e: &&str| e.to_string())
            .contains("SubClassOf( A B )"));

        // The default NoProgressMonitor is also accepted and is a no-op.
        let mut subsumers2: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers2.insert("top", ["top"].into_iter().collect());
        subsumers2.insert("bottom", ["top", "bottom"].into_iter().collect());
        let _ = build_hierarchy_with_monitor("top", "bottom", subsumers2, &mut NoProgressMonitor);
    }

    #[test]
    fn dump_functional_syntax_brackets_and_skips() {
        // A ⊑ B, plus an equivalent pair {P, Q} unrelated to A/B.
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top", ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "A", "B", "P", "Q", "bottom"].into_iter().collect());
        subsumers.insert("A", ["A", "B", "top"].into_iter().collect());
        subsumers.insert("B", ["B", "top"].into_iter().collect());
        subsumers.insert("P", ["P", "Q", "top"].into_iter().collect());
        subsumers.insert("Q", ["Q", "P", "top"].into_iter().collect());
        let hierarchy = build_hierarchy("top", "bottom", subsumers);

        let dump = hierarchy.dump_functional_syntax(
            "EquivalentClasses",
            "SubClassOf",
            |e| format!("<{e}>"),
        );
        // P and Q collapse to one node -> an EquivalentClasses axiom.
        assert!(dump.contains("EquivalentClasses( <P> <Q> )"), "{dump}");
        // A ⊑ B edge is dumped with brackets.
        assert!(dump.contains("SubClassOf( <A> <B> )"), "{dump}");
        // Edges into bottom are skipped: no SubClassOf( <bottom> ... ).
        assert!(!dump.contains("<bottom>"), "bottom edges should be skipped: {dump}");
        // Edges whose super is top are skipped too (HermiT omits `... THING`),
        // so B ⊑ top and P ⊑ top never appear.
        assert!(!dump.contains("<top>"), "top-as-super edges should be skipped: {dump}");

        // Byte-for-byte pinned dump: sorted lines, `keyword( ... )` inner-paren
        // spacing exactly as HermiT's HierarchyDumperFSS, EquivalentClasses
        // members sorted, edges into bottom and edges into top both dropped.
        // Each section ends with \n\n: one \n per axiom (println) plus the
        // trailing blank line from m_out.println() at HierarchyDumperFSS.java:73.
        let expected = "EquivalentClasses( <P> <Q> )\nSubClassOf( <A> <B> )\n\n";
        assert_eq!(dump, expected, "got:\n{dump}");
    }

    #[test]
    fn dump_functional_syntax_java_data_malformed_equiv_tail() {
        // Byte-pinned: Java's HierarchyDumperFSS.printDataPropertyHierarchy has a
        // bug at line 127 where non-first EquivalentDataProperties members are
        // emitted as ">iri>" (leading '>') instead of "<iri>".
        // d1 ⊑ d2 is a sub-property; d3 and d4 are equivalent.
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top",    ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "d1", "d2", "d3", "d4", "bottom"].into_iter().collect());
        subsumers.insert("d1",     ["d1", "d2", "top"].into_iter().collect());
        subsumers.insert("d2",     ["d2", "top"].into_iter().collect());
        subsumers.insert("d3",     ["d3", "d4", "top"].into_iter().collect());
        subsumers.insert("d4",     ["d4", "d3", "top"].into_iter().collect());
        let hierarchy = build_hierarchy("top", "bottom", subsumers);

        let dump = hierarchy.dump_functional_syntax_java_data(
            "EquivalentDataProperties",
            "SubDataPropertyOf",
            |e: &&str| format!("<{e}>"),
            |e: &&str| format!(">{}>", e),
        );
        // Non-first equivalent member uses ">iri>" (Java bug reproduction).
        assert!(dump.contains("EquivalentDataProperties( <d3> >d4> )"), "got: {dump}");
        // Sub-property edges use the normal "<iri>" form.
        assert!(dump.contains("SubDataPropertyOf( <d1> <d2> )"), "got: {dump}");
        // Byte-pinned expected content (ignoring trailing whitespace).
        let expected = "\
EquivalentDataProperties( <d3> >d4> )
SubDataPropertyOf( <d1> <d2> )";
        assert_eq!(dump.trim(), expected, "got:\n{dump}");
    }

    #[test]
    fn fresh_element_queries_use_synthetic_thing_nothing_node() {
        // A class absent from the classified hierarchy must behave like
        // HermiT's synthetic fresh node (equivalent={self}, supers={top},
        // subs={bottom}), not return empty.
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top", ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "A", "bottom"].into_iter().collect());
        subsumers.insert("A", ["A", "top"].into_iter().collect());
        let hierarchy = build_hierarchy("top", "bottom", subsumers);

        // "Fresh" is not in the hierarchy.
        assert_eq!(
            hierarchy.equivalent_elements_of(&"Fresh"),
            ["Fresh"].into_iter().collect::<Set<_>>()
        );
        assert_eq!(
            hierarchy.super_elements(&"Fresh", false),
            ["top"].into_iter().collect::<Set<_>>()
        );
        assert_eq!(
            hierarchy.super_elements(&"Fresh", true),
            ["top"].into_iter().collect::<Set<_>>()
        );
        assert_eq!(
            hierarchy.sub_elements(&"Fresh", false),
            ["bottom"].into_iter().collect::<Set<_>>()
        );
        assert_eq!(
            hierarchy.sub_elements(&"Fresh", true),
            ["bottom"].into_iter().collect::<Set<_>>()
        );
    }

    #[test]
    fn find_position_locates_a_fresh_element() {
        // Existing hierarchy: A ⊑ B (top > B > A > bottom).
        let mut subsumers: HashMap<&str, HashSet<&str>> = HashMap::new();
        subsumers.insert("top", ["top"].into_iter().collect());
        subsumers.insert("bottom", ["top", "A", "B", "bottom"].into_iter().collect());
        subsumers.insert("A", ["A", "B", "top"].into_iter().collect());
        subsumers.insert("B", ["B", "top"].into_iter().collect());
        let hierarchy = build_hierarchy("top", "bottom", subsumers);

        // Subsumption oracle over {top, A, B, bottom, C}: define C with A ⊑ C ⊑ B
        // (strictly between A and B). does_subsume(parent, child).
        let subs: HashMap<&str, HashSet<&str>> = {
            let mut m: HashMap<&str, HashSet<&str>> = HashMap::new();
            m.insert("top", ["top"].into_iter().collect());
            m.insert("B", ["B", "top"].into_iter().collect());
            m.insert("C", ["C", "B", "top"].into_iter().collect());
            m.insert("A", ["A", "C", "B", "top"].into_iter().collect());
            m.insert("bottom", ["bottom", "A", "C", "B", "top"].into_iter().collect());
            m
        };
        let does_subsume = |parent: &&str, child: &&str| subs[*child].contains(*parent);

        let pos = hierarchy.find_position(&"C", does_subsume);
        match pos {
            Position::Between { parents, children } => {
                let b_node = hierarchy.node_for_element(&"B").unwrap();
                let a_node = hierarchy.node_for_element(&"A").unwrap();
                assert!(parents.contains(&b_node), "C's parent should be B");
                assert!(children.contains(&a_node), "C's child should be A");
            }
            Position::Existing(n) => panic!("expected a fresh position, got existing node {n}"),
        }

        // An element equivalent to B (B ⊑ X and X ⊑ B) lands on B's node.
        let subs2: HashMap<&str, HashSet<&str>> = {
            let mut m: HashMap<&str, HashSet<&str>> = HashMap::new();
            m.insert("top", ["top"].into_iter().collect());
            m.insert("X", ["X", "B", "top"].into_iter().collect());
            m.insert("B", ["B", "X", "top"].into_iter().collect());
            m.insert("A", ["A", "B", "X", "top"].into_iter().collect());
            m.insert("bottom", ["bottom", "A", "B", "X", "top"].into_iter().collect());
            m
        };
        let does_subsume2 = |parent: &&str, child: &&str| subs2[*child].contains(*parent);
        let pos2 = hierarchy.find_position(&"X", does_subsume2);
        assert_eq!(pos2, Position::Existing(hierarchy.node_for_element(&"B").unwrap()));
    }
}
