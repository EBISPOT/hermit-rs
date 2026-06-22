// Ports of org.semanticweb.HermiT.model.{DescriptionGraph,DescriptionGraph.Edge,
// ExistsDescriptionGraph}.

use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use crate::model::atom::Atom;
use crate::model::clause::DLClause;
use crate::model::concept::AtomicConcept;
use crate::model::predicate::DLPredicate;
use crate::model::role::AtomicRole;
use crate::model::term::{Term, Variable};
use crate::prefixes::Prefixes;
use crate::impl_display_prefixes;

// ---------------------------------------------------------------------------
// DescriptionGraph
// ---------------------------------------------------------------------------
//
// Unlike the other model classes, DescriptionGraph is NOT interned: in HermiT
// it does not override equals/hashCode, so it uses Java object identity. We
// reproduce that with an `Arc` whose equality and hashing are pointer-based;
// each `new` call yields a distinct identity.

#[derive(Debug)]
pub struct DescriptionGraphData {
    name: String,
    atomic_concepts_by_vertices: Vec<AtomicConcept>,
    edges: Vec<Edge>,
    start_concepts: HashSet<AtomicConcept>,
}

// A `Copy` handle that is a plain pointer to a leaked, identity-distinct
// allocation -- mirroring Java's object identity (each `new` is a distinct
// instance) without `Arc`'s atomic reference counting. There are very few
// description graphs, so leaking them (they live for the whole run, as the Java
// instances effectively do) costs nothing.
#[derive(Clone, Copy)]
pub struct DescriptionGraph(&'static DescriptionGraphData);

impl PartialEq for DescriptionGraph {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}
impl Eq for DescriptionGraph {}
impl Hash for DescriptionGraph {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0 as *const DescriptionGraphData as usize).hash(state);
    }
}
impl std::fmt::Debug for DescriptionGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DescriptionGraph({})", self.0.name)
    }
}

impl DescriptionGraph {
    pub fn new(
        name: impl Into<String>,
        atomic_concepts_by_vertices: Vec<AtomicConcept>,
        edges: Vec<Edge>,
        start_concepts: HashSet<AtomicConcept>,
    ) -> DescriptionGraph {
        DescriptionGraph(Box::leak(Box::new(DescriptionGraphData {
            name: name.into(),
            atomic_concepts_by_vertices,
            edges,
            start_concepts,
        })))
    }
    pub fn name(&self) -> &str {
        &self.0.name
    }
    /// The canonical leaked-allocation address, a stable per-value word id (one
    /// allocation per distinct graph), consistent with this type's identity
    /// `Eq`/`Hash`. Used as a cheap hash key on the hot tuple-index path.
    #[inline]
    pub fn intern_ptr(&self) -> usize {
        self.0 as *const DescriptionGraphData as usize
    }
    pub fn arity(&self) -> usize {
        self.0.atomic_concepts_by_vertices.len()
    }
    pub fn get_atomic_concept_for_vertex(&self, vertex: usize) -> &AtomicConcept {
        &self.0.atomic_concepts_by_vertices[vertex]
    }
    pub fn number_of_vertices(&self) -> usize {
        self.0.atomic_concepts_by_vertices.len()
    }
    pub fn number_of_edges(&self) -> usize {
        self.0.edges.len()
    }
    pub fn get_edge(&self, edge_index: usize) -> &Edge {
        &self.0.edges[edge_index]
    }
    pub fn get_start_concepts(&self) -> &HashSet<AtomicConcept> {
        &self.0.start_concepts
    }
    pub fn produce_start_dl_clauses(&self, resulting_dl_clauses: &mut indexmap::IndexSet<DLClause>) {
        let x = Variable::create("X");
        for start_atomic_concept in &self.0.start_concepts {
            let antecedent = vec![Atom::create(
                DLPredicate::AtomicConcept(start_atomic_concept.clone()),
                vec![Term::Variable(x.clone())],
            )];
            let mut consequent = Vec::new();
            for vertex in 0..self.0.atomic_concepts_by_vertices.len() {
                if &self.0.atomic_concepts_by_vertices[vertex] == start_atomic_concept {
                    consequent.push(Atom::create(
                        DLPredicate::ExistsDescriptionGraph(ExistsDescriptionGraph::create(
                            self.clone(),
                            vertex as i32,
                        )),
                        vec![Term::Variable(x.clone())],
                    ));
                }
            }
            resulting_dl_clauses.insert(DLClause::create(consequent, antecedent));
        }
    }
    pub fn to_string_prefixes(&self, ns: &Prefixes) -> String {
        ns.abbreviate_iri(&self.0.name)
    }
    pub fn get_text_representation(&self) -> String {
        let mut buffer = String::from("[\n");
        for vertex in 0..self.0.atomic_concepts_by_vertices.len() {
            buffer.push_str("   ");
            buffer.push_str(&vertex.to_string());
            buffer.push_str(" --> ");
            buffer.push_str(self.0.atomic_concepts_by_vertices[vertex].iri());
            buffer.push('\n');
        }
        buffer.push('\n');
        for edge in &self.0.edges {
            buffer.push_str("  ");
            buffer.push_str(&edge.get_from_vertex().to_string());
            buffer.push_str(" -- ");
            buffer.push_str(edge.get_atomic_role().iri());
            buffer.push_str(" --> ");
            buffer.push_str(&edge.get_to_vertex().to_string());
            buffer.push('\n');
        }
        buffer.push('\n');
        for atomic_concept in &self.0.start_concepts {
            buffer.push_str("  ");
            buffer.push_str(atomic_concept.iri());
            buffer.push('\n');
        }
        buffer.push(']');
        buffer
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Edge {
    atomic_role: AtomicRole,
    from_vertex: i32,
    to_vertex: i32,
}

impl Edge {
    pub fn new(atomic_role: AtomicRole, from_vertex: i32, to_vertex: i32) -> Edge {
        Edge { atomic_role, from_vertex, to_vertex }
    }
    pub fn get_atomic_role(&self) -> &AtomicRole {
        &self.atomic_role
    }
    pub fn get_from_vertex(&self) -> i32 {
        self.from_vertex
    }
    pub fn get_to_vertex(&self) -> i32 {
        self.to_vertex
    }
}

// ---------------------------------------------------------------------------
// ExistsDescriptionGraph
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct ExistsDescriptionGraphData {
    description_graph: DescriptionGraph,
    vertex: i32,
}

crate::interned!(pub ExistsDescriptionGraph => ExistsDescriptionGraphData);

impl ExistsDescriptionGraph {
    pub fn create(description_graph: DescriptionGraph, vertex: i32) -> ExistsDescriptionGraph {
        ExistsDescriptionGraph::intern(ExistsDescriptionGraphData { description_graph, vertex })
    }
    pub fn get_description_graph(&self) -> &DescriptionGraph {
        &self.0.description_graph
    }
    pub fn get_vertex(&self) -> i32 {
        self.0.vertex
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn is_always_true(&self) -> bool {
        false
    }
    pub fn is_always_false(&self) -> bool {
        false
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        format!(
            "exists({}|{})",
            prefixes.abbreviate_iri(self.0.description_graph.name()),
            self.0.vertex
        )
    }
}

impl_display_prefixes!(DescriptionGraph, ExistsDescriptionGraph);
