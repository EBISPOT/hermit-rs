// Port of the org.semanticweb.HermiT.datalog package: a *materializing* engine
// for DL-safe conjunctive-query answering over the deterministic Horn fragment.
//
// This mirrors HermiT's `DatalogEngine` (`DatalogEngine.java`) and
// `ConjunctiveQuery` (`ConjunctiveQuery.java`):
//
//   * The engine is built over a *clausified* `DLOntology` (not the raw
//     `SetOntology`). Its constructor REJECTS ontologies whose DL-clauses have a
//     disjunctive head (head length > 1) -- Java throws
//     `IllegalArgumentException("...rules with disjunctive heads.")`
//     (DatalogEngine.java:35-37).
//   * `materialize()` computes the deterministic Horn closure ONCE: it builds a
//     single tableau with the *null existential strategy* (no existential
//     expansion), saturates it, records the term->node mapping and the
//     term equivalence classes / representatives, and returns whether the model
//     is clash-free (DatalogEngine.java:48-73). A clash means the ontology is
//     unsatisfiable.
//   * A `ConjunctiveQuery` is evaluated by reading certain answers off the
//     materialized extension tables, rather than by re-running per-binding
//     entailment (ConjunctiveQuery.java).
//

use std::collections::HashMap;

use horned_owl::model::{ClassExpression as CE, ObjectPropertyExpression as OPE};
use horned_owl::ontology::set::SetOntology;

use crate::model::{
    AtomicConcept, AtomicRole, Concept, DLOntology, DLPredicate, Individual, Role, Term,
};
use crate::structural::A;
use crate::tableau::dependency_set::DependencySet;
use crate::tableau::node::NodeId;
use crate::tableau::object::TableauObject;
use crate::tableau::{HyperresolutionManager, Tableau};

/// A query term: a variable or a concrete named individual (by IRI).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum QueryTerm {
    Variable(String),
    Individual(String),
}

/// A conjunctive-query atom.
///
/// Mirrors the atom kinds an `org.semanticweb.HermiT.model.Atom` query atom can
/// carry over the clausified vocabulary. The port covers:
///   * `Concept`     -- a unary atomic-concept atom `C(t)` (`AtomicConcept`).
///   * `Role`        -- a binary object-role atom `r(s,t)` (`AtomicRole`).
///   * `Equality`    -- `t1 == t2` (the `Equality` DL predicate).
///   * `Inequality`  -- `t1 != t2` (the `Inequality` DL predicate).
///
/// Horned-owl limitation: Java query atoms can also range over *data*
/// predicates (`AtomicRole` on data properties, datatype atoms). The port's
/// materialized model keys data on `Constant` nodes; data-property query atoms
/// are not exposed here because horned-owl's `ObjectPropertyExpression` /
/// `ClassExpression` query surface does not carry a data-property atom kind that
/// round-trips to the clausified data vocabulary. Concept atoms accept arbitrary
/// `ClassExpression`s for API compatibility, but only *named* classes
/// (`CE::Class`) are read off the materialized model (matching Java's
/// `AtomicConcept` query atoms); a non-atomic class expression is reported as an
/// unsupported-atom error rather than silently mis-answered.
#[derive(Clone, Debug)]
pub enum QueryAtom {
    Concept(CE<A>, QueryTerm),
    Role(OPE<A>, QueryTerm, QueryTerm),
    Equality(QueryTerm, QueryTerm),
    Inequality(QueryTerm, QueryTerm),
}

impl QueryAtom {
    fn terms(&self) -> Vec<&QueryTerm> {
        match self {
            QueryAtom::Concept(_, t) => vec![t],
            QueryAtom::Role(_, a, b) => vec![a, b],
            QueryAtom::Equality(a, b) => vec![a, b],
            QueryAtom::Inequality(a, b) => vec![a, b],
        }
    }
}

/// Port of `QueryResultCollector`: notified of each answer tuple (the bindings
/// of the answer variables, in order).
///
/// An answer position is `Some(iri)` when the corresponding answer variable was
/// bound by a concept/role retrieval, and `None` when it was *not* bound by any
/// body atom. The `None` case mirrors Java's `QueryAnswerCallback.execute`: a
/// disconnected answer variable leaves its values-buffer slot unset, so
/// `m_nodesToTerms.get(null)` is `null` and the result column is `null`
/// (ConjunctiveQuery.java `compileHeads` / `QueryAnswerCallback`). Exactly one
/// answer row carries that unbound column -- the variable is never enumerated
/// over the named individuals.
pub trait QueryResultCollector {
    fn process_result(&mut self, answer: &[Option<String>]);
}

/// Convenience collector that preserves the bound/unbound distinction: an
/// unbound answer position (Java's `null`) is kept as `None`.
impl QueryResultCollector for Vec<Vec<Option<String>>> {
    fn process_result(&mut self, answer: &[Option<String>]) {
        self.push(answer.to_vec());
    }
}

/// Backward-compatible collector for callers that only ever query fully-bound
/// answer variables (every answer variable occurs in a concept/role atom). An
/// unbound position (Java's `null`) has no `String` representation here, so it
/// is rendered as the empty string; such callers never produce one.
impl QueryResultCollector for Vec<Vec<String>> {
    fn process_result(&mut self, answer: &[Option<String>]) {
        self.push(
            answer
                .iter()
                .map(|cell| cell.clone().unwrap_or_default())
                .collect(),
        );
    }
}

/// Port of `ConjunctiveQuery`: a conjunction of atoms with distinguished answer
/// variables.
///
/// Java's `ConjunctiveQuery` constructor calls `datalogEngine.materialize()` and
/// throws `IllegalStateException("...unsatisfiable.")` when materialization
/// signals a clash (ConjunctiveQuery.java:30-31); the port reproduces this in
/// [`ConjunctiveQuery::evaluate`], which materializes the engine on first use.
pub struct ConjunctiveQuery {
    atoms: Vec<QueryAtom>,
    /// The distinguished answer terms (`ConjunctiveQuery.m_answerTerms`, a
    /// `Term[]`). A `Variable` answer term is bound by the join; an `Individual`
    /// (constant) answer term echoes the constant into its result column, exactly
    /// as Java's `compileHeads` leaves a non-`Variable` answer term untouched.
    answer_terms: Vec<QueryTerm>,
}

impl ConjunctiveQuery {
    pub fn new(atoms: Vec<QueryAtom>, answer_terms: Vec<QueryTerm>) -> ConjunctiveQuery {
        ConjunctiveQuery { atoms, answer_terms }
    }

    /// The atomic concept named by a concept query atom's class expression, or an
    /// error for a non-named class (only named classes round-trip to the
    /// clausified query vocabulary, matching Java's `AtomicConcept` query atoms).
    fn concept_of(class_expression: &CE<A>) -> Result<AtomicConcept, String> {
        match class_expression {
            CE::Class(c) => Ok(AtomicConcept::create(c.0.to_string())),
            _ => Err(
                "DatalogEngine query concept atoms must be named classes; \
                 complex class expressions are not part of the clausified query \
                 vocabulary"
                    .to_string(),
            ),
        }
    }

    /// The role named by a role query atom's object-property expression.
    fn role_of(ope: &OPE<A>) -> Role {
        match ope {
            OPE::ObjectProperty(p) => Role::AtomicRole(AtomicRole::create(p.0.to_string())),
            OPE::InverseObjectProperty(p) => Role::InverseRole(
                crate::model::InverseRole::create(AtomicRole::create(p.0.to_string())),
            ),
        }
    }

    /// Evaluates the query over the (materialized) `engine`, reporting each
    /// certain answer (a binding of the answer variables to named individuals)
    /// to `collector`.
    ///
    /// Faithful to `ConjunctiveQuery.evaluate` (ConjunctiveQuery.java:65-77) and
    /// its constructor (ConjunctiveQuery.java:30-48): the body atoms are reordered
    /// by selectivity via `HyperresolutionManager.BodyAtomsSwapper` and then
    /// compiled into an indexed nested-loop join (the
    /// `DLClauseEvaluator.ConjunctionCompiler` worker program), so each unbound
    /// concept/role variable binds only to actual successors in the materialized
    /// extension tables -- not to every named individual. The join here is the
    /// recursive equivalent of that compiled worker VM.
    ///
    /// Materializes the engine on first use (Java's `ConjunctiveQuery`
    /// constructor calls `materialize()`); a clash during materialization means
    /// the ontology is unsatisfiable, reported as an `Err`
    /// (ConjunctiveQuery.java:30-31, DatalogEngine.java:48-73).
    pub fn evaluate(
        &self,
        engine: &DatalogEngine,
        collector: &mut dyn QueryResultCollector,
    ) -> Result<(), String> {
        let materialization = engine.materialize()?;

        // Java answers by joining the materialized extension tables: each query
        // variable binds to a tableau *node*, which is mapped back to a single
        // representative term via `m_nodesToTerms` (DatalogEngine.java:56-57,
        // ConjunctiveQuery.QueryAnswerCallback). Merged individuals therefore
        // collapse to one answer. Use the SINGLE precomputed `node -> term` map
        // (`Materialization::node_to_term`, the port of `m_nodesToTerms`) so the
        // query path and `getRepresentative` / `getEquivalenceClass` are mutually
        // consistent. Java performs NO enumeration over the named individuals: a
        // query variable is bound only by a concept/role retrieval, and an answer
        // variable that occurs in no body atom is reported once as `null`
        // (see `emit_answers`), so there is no representatives list to range over.
        let node_to_representative = &materialization.node_to_term;

        // BodyAtomsSwapper: reorder the body atoms so the most selective bound
        // atom comes first and each subsequent atom shares variables already
        // bound (HyperresolutionManager.java:258-360, getSwappedDLClause /
        // getAtomGoodness). Validate concept atoms (named classes only) up front,
        // matching the constructor-time vocabulary check.
        for atom in &self.atoms {
            if let QueryAtom::Concept(class_expression, _) = atom {
                Self::concept_of(class_expression)?;
            }
            // DLClauseEvaluator.ValuesBufferManager (DLClauseEvaluator.java:175-178):
            // every non-variable body term must map to a known node, else
            // "Term '...' is unknown to the reasoner." Mirror that here -- a query
            // constant absent from the materialized ABox is an error, not silently
            // zero answers.
            for term in atom.terms() {
                if let QueryTerm::Individual(iri) = term {
                    if materialization.node_for_iri(iri).is_none() {
                        return Err(format!("Term '{iri}' is unknown to the reasoner."));
                    }
                }
            }
        }
        let ordered = swap_body_atoms(&self.atoms);

        let mut binding: HashMap<String, String> = HashMap::new();
        let mut bound_so_far: std::collections::HashSet<String> = std::collections::HashSet::new();
        // The canonical node each retrieval-bound variable was bound to. Mirrors
        // Java's values buffer, which holds tableau *nodes* (not terms): a
        // variable is bound to a node even when that node carries no term, and
        // only mapped back through `m_nodesToTerms` (possibly to `null`) when the
        // answer row is written (ConjunctiveQuery.QueryAnswerCallback.execute).
        // `binding` (above) is the IRI view used for emission/representatives and
        // is absent for a variable bound to a term-less node (Java's `null`).
        let mut node_binding: HashMap<String, NodeId> = HashMap::new();
        self.join(
            engine,
            &materialization,
            &node_to_representative,
            &ordered,
            0,
            &mut binding,
            &mut bound_so_far,
            &mut node_binding,
            collector,
        );
        Ok(())
    }

    /// The indexed nested-loop join over the swapped body atoms. Mirrors the
    /// worker program produced by `DLClauseEvaluator.ConjunctionCompiler`
    /// (DLClauseEvaluator.java:842-911 `compileBodyAtom`): concept/role atoms are
    /// retrievals bound on the already-bound variables (so unbound variables range
    /// only over matching extension-table tuples), and `compileHeads` /
    /// `QueryAnswerCallback` emits the answer tuple once every atom is matched.
    #[allow(clippy::too_many_arguments)]
    fn join(
        &self,
        engine: &DatalogEngine,
        materialization: &Materialization,
        node_to_representative: &HashMap<NodeId, Individual>,
        ordered: &[QueryAtom],
        atom_index: usize,
        binding: &mut HashMap<String, String>,
        bound_so_far: &mut std::collections::HashSet<String>,
        node_binding: &mut HashMap<String, NodeId>,
        collector: &mut dyn QueryResultCollector,
    ) {
        if atom_index == ordered.len() {
            // compileHeads / QueryAnswerCallback: emit one answer tuple. An answer
            // variable not pinned by any concept/role retrieval is emitted as an
            // unbound column (Java `null`), NOT enumerated over the individuals.
            self.emit_answers(binding, bound_so_far, collector);
            return;
        }
        let atom = &ordered[atom_index];
        match atom {
            QueryAtom::Concept(class_expression, term) => {
                let concept = Self::concept_of(class_expression)
                    .expect("concept atoms validated in evaluate");
                self.match_concept_atom(
                    engine,
                    materialization,
                    node_to_representative,
                    ordered,
                    atom_index,
                    &Concept::AtomicConcept(concept),
                    term,
                    binding,
                    bound_so_far,
                    node_binding,
                    collector,
                );
            }
            QueryAtom::Role(ope, from, to) => {
                let role = Self::role_of(ope);
                self.match_role_atom(
                    engine,
                    materialization,
                    node_to_representative,
                    ordered,
                    atom_index,
                    &role,
                    from,
                    to,
                    binding,
                    bound_so_far,
                    node_binding,
                    collector,
                );
            }
            // Java compiles Equality/Inequality query atoms through the *general*
            // `compileBodyAtom` branch (DLClauseEvaluator.java:842-911): a retrieval
            // over `getExtensionTable(arity)` keyed on the comparison predicate,
            // exactly like a role atom. Equality assertions merge nodes rather than
            // being stored, so the Equality extension is empty (a query whose body
            // mentions an Equality atom yields no answers); Inequality assertions are
            // stored (in the asserted direction), so an Inequality atom retrieves and
            // can bind over those stored pairs.
            QueryAtom::Equality(from, to) => {
                self.match_comparison_atom(
                    engine, materialization, node_to_representative, ordered, atom_index,
                    DLPredicate::Equality, from, to,
                    binding, bound_so_far, node_binding, collector,
                );
            }
            QueryAtom::Inequality(from, to) => {
                self.match_comparison_atom(
                    engine, materialization, node_to_representative, ordered, atom_index,
                    DLPredicate::Inequality, from, to,
                    binding, bound_so_far, node_binding, collector,
                );
            }
        }
    }

    /// A comparison-atom (`Equality` / `Inequality`) retrieval, mirroring
    /// [`match_role_atom`] but keyed on a `DLPredicate` over the ternary extension
    /// table (HermiT compiles these uniformly via `compileBodyAtom`; they are not
    /// special-cased). With both terms bound it is a `containsAssertion` membership
    /// check; otherwise it scans the predicate's extension, binding each unbound
    /// term to the matched (canonical) node.
    #[allow(clippy::too_many_arguments)]
    fn match_comparison_atom(
        &self,
        engine: &DatalogEngine,
        materialization: &Materialization,
        node_to_representative: &HashMap<NodeId, Individual>,
        ordered: &[QueryAtom],
        atom_index: usize,
        predicate: DLPredicate,
        from: &QueryTerm,
        to: &QueryTerm,
        binding: &mut HashMap<String, String>,
        bound_so_far: &mut std::collections::HashSet<String>,
        node_binding: &mut HashMap<String, NodeId>,
        collector: &mut dyn QueryResultCollector,
    ) {
        let from_bound = !matches!(from, QueryTerm::Variable(v) if !bound_so_far.contains(v));
        let to_bound = !matches!(to, QueryTerm::Variable(v) if !bound_so_far.contains(v));
        let resolve_bound = |t: &QueryTerm| -> Option<NodeId> {
            match t {
                QueryTerm::Variable(v) => node_binding
                    .get(v)
                    .copied()
                    .or_else(|| binding.get(v).and_then(|iri| materialization.node_for_iri(iri))),
                QueryTerm::Individual(i) => materialization.node_for_iri(i),
            }
        };
        let from_node = if from_bound { resolve_bound(from) } else { None };
        let to_node = if to_bound { resolve_bound(to) } else { None };
        if (from_bound && from_node.is_none()) || (to_bound && to_node.is_none()) {
            return;
        }
        // Both bound: fully-indexed containment check (compileBodyAtom with every
        // argument a bound binding position).
        if from_bound && to_bound {
            if materialization.comparison_holds_nodes(
                predicate,
                from_node.unwrap(),
                to_node.unwrap(),
            ) {
                self.join(
                    engine, materialization, node_to_representative, ordered,
                    atom_index + 1, binding, bound_so_far, node_binding, collector,
                );
            }
            return;
        }
        for (a, b) in materialization.comparison_extension(predicate) {
            if let Some(fixed) = from_node {
                if a != fixed {
                    continue;
                }
            }
            if let Some(fixed) = to_node {
                if b != fixed {
                    continue;
                }
            }
            let mut newly_bound: Vec<String> = Vec::new();
            let mut ok = true;
            if !from_bound {
                if let QueryTerm::Variable(v) = from {
                    if let Some(&existing) = node_binding.get(v) {
                        if existing != a {
                            ok = false;
                        }
                    } else {
                        Self::bind_role_endpoint(
                            v, a, node_to_representative, binding, bound_so_far, node_binding,
                        );
                        newly_bound.push(v.clone());
                    }
                }
            }
            if ok && !to_bound {
                if let QueryTerm::Variable(v) = to {
                    if let Some(&existing) = node_binding.get(v) {
                        if existing != b {
                            ok = false;
                        }
                    } else {
                        Self::bind_role_endpoint(
                            v, b, node_to_representative, binding, bound_so_far, node_binding,
                        );
                        newly_bound.push(v.clone());
                    }
                }
            }
            if ok {
                self.join(
                    engine, materialization, node_to_representative, ordered,
                    atom_index + 1, binding, bound_so_far, node_binding, collector,
                );
            }
            for v in newly_bound {
                binding.remove(&v);
                bound_so_far.remove(&v);
                node_binding.remove(&v);
            }
        }
    }

    /// A `C(t)` retrieval: if `t` is already bound, test membership; otherwise
    /// iterate the concept's extension over the representative-mapped nodes,
    /// binding `t` to each matching named individual.
    #[allow(clippy::too_many_arguments)]
    fn match_concept_atom(
        &self,
        engine: &DatalogEngine,
        materialization: &Materialization,
        node_to_representative: &HashMap<NodeId, Individual>,
        ordered: &[QueryAtom],
        atom_index: usize,
        concept: &Concept,
        term: &QueryTerm,
        binding: &mut HashMap<String, String>,
        bound_so_far: &mut std::collections::HashSet<String>,
        node_binding: &mut HashMap<String, NodeId>,
        collector: &mut dyn QueryResultCollector,
    ) {
        let unbound_var = match term {
            QueryTerm::Variable(v) if !bound_so_far.contains(v) => Some(v.clone()),
            _ => None,
        };
        match unbound_var {
            // Already bound (or a constant): test the single binding.
            None => {
                let node = match term {
                    QueryTerm::Variable(v) => node_binding
                        .get(v)
                        .copied()
                        .or_else(|| binding.get(v).and_then(|iri| materialization.node_for_iri(iri))),
                    QueryTerm::Individual(i) => materialization.node_for_iri(i),
                };
                if let Some(node) = node {
                    if materialization.concept_holds_node(concept_as_atomic(concept), node) {
                        self.join(
                            engine, materialization, node_to_representative, ordered,
                            atom_index + 1, binding, bound_so_far, node_binding, collector,
                        );
                    }
                }
            }
            // Unbound: bind to every node that carries this concept. The retrieval
            // yields canonical nodes; bind the variable to that node (via
            // `node_binding`, mirroring Java's values buffer, which holds nodes)
            // and -- when the node carries a term -- to its representative IRI.
            // A2: a node with NO representative term still binds the variable and
            // still emits its row; the answer column is reported as `null`/`None`
            // (`m_nodesToTerms.get(node)` is `null`), it is NOT dropped.
            Some(variable) => {
                for (node, _node) in materialization.concept_extension(concept) {
                    node_binding.insert(variable.clone(), node);
                    bound_so_far.insert(variable.clone());
                    match node_to_representative.get(&node) {
                        Some(representative) => {
                            binding.insert(variable.clone(), representative.iri().to_string());
                        }
                        None => {
                            binding.remove(&variable);
                        }
                    }
                    self.join(
                        engine, materialization, node_to_representative,
                        ordered, atom_index + 1, binding, bound_so_far, node_binding, collector,
                    );
                }
                binding.remove(&variable);
                bound_so_far.remove(&variable);
                node_binding.remove(&variable);
            }
        }
    }

    /// A `r(s,t)` retrieval, bound on whichever of `s` / `t` is already bound.
    #[allow(clippy::too_many_arguments)]
    fn match_role_atom(
        &self,
        engine: &DatalogEngine,
        materialization: &Materialization,
        node_to_representative: &HashMap<NodeId, Individual>,
        ordered: &[QueryAtom],
        atom_index: usize,
        role: &Role,
        from: &QueryTerm,
        to: &QueryTerm,
        binding: &mut HashMap<String, String>,
        bound_so_far: &mut std::collections::HashSet<String>,
        node_binding: &mut HashMap<String, NodeId>,
        collector: &mut dyn QueryResultCollector,
    ) {
        let from_bound = !matches!(from, QueryTerm::Variable(v) if !bound_so_far.contains(v));
        let to_bound = !matches!(to, QueryTerm::Variable(v) if !bound_so_far.contains(v));

        // Resolve a bound endpoint to its canonical node: a variable through
        // `node_binding` (the node it was retrieval-bound to, which exists even
        // for a term-less node -- the A2 case), a constant through its loaded
        // node. An unmapped bound endpoint cannot match any role tuple.
        let resolve_bound = |t: &QueryTerm| -> Option<NodeId> {
            match t {
                QueryTerm::Variable(v) => node_binding
                    .get(v)
                    .copied()
                    .or_else(|| binding.get(v).and_then(|iri| materialization.node_for_iri(iri))),
                QueryTerm::Individual(i) => materialization.node_for_iri(i),
            }
        };
        let from_node = if from_bound { resolve_bound(from) } else { None };
        let to_node = if to_bound { resolve_bound(to) } else { None };
        if (from_bound && from_node.is_none()) || (to_bound && to_node.is_none()) {
            return;
        }

        // Both endpoints bound: an indexed (fully-bound) containment check rather
        // than a scan of the role extension (the indexed retrieval of
        // compileBodyAtom when every argument is a bound binding position).
        if from_bound && to_bound {
            if materialization
                .role_holds_nodes(role, from_node.unwrap(), to_node.unwrap())
            {
                self.join(
                    engine, materialization, node_to_representative, ordered,
                    atom_index + 1, binding, bound_so_far, node_binding, collector,
                );
            }
            return;
        }

        for (a, b) in materialization.role_extension(role) {
            if let Some(fixed) = from_node {
                if a != fixed {
                    continue;
                }
            }
            if let Some(fixed) = to_node {
                if b != fixed {
                    continue;
                }
            }
            // Bind any unbound endpoint variable to the matched node (mirroring
            // Java's values buffer, which holds *nodes*). A2: a node carrying NO
            // representative term still binds the variable and the row is still
            // emitted -- the answer column is reported as `null`/`None`
            // (`m_nodesToTerms.get(node)` is `null`), NOT dropped. When the same
            // variable is both endpoints, the two matched nodes must agree.
            let mut newly_bound: Vec<String> = Vec::new();
            let mut ok = true;
            if !from_bound {
                if let QueryTerm::Variable(v) = from {
                    if let Some(&existing) = node_binding.get(v) {
                        // Already bound earlier in this same tuple (v is both
                        // endpoints): require the nodes to coincide.
                        if existing != a {
                            ok = false;
                        }
                    } else {
                        Self::bind_role_endpoint(
                            v, a, node_to_representative, binding, bound_so_far, node_binding,
                        );
                        newly_bound.push(v.clone());
                    }
                }
            }
            if ok && !to_bound {
                if let QueryTerm::Variable(v) = to {
                    if let Some(&existing) = node_binding.get(v) {
                        if existing != b {
                            ok = false;
                        }
                    } else {
                        Self::bind_role_endpoint(
                            v, b, node_to_representative, binding, bound_so_far, node_binding,
                        );
                        newly_bound.push(v.clone());
                    }
                }
            }
            if ok {
                self.join(
                    engine, materialization, node_to_representative, ordered,
                    atom_index + 1, binding, bound_so_far, node_binding, collector,
                );
            }
            for v in newly_bound {
                binding.remove(&v);
                bound_so_far.remove(&v);
                node_binding.remove(&v);
            }
        }
    }

    /// Binds the role-endpoint variable `v` to the canonical `node` it matched:
    /// records the node in `node_binding` (Java's values buffer) and, when the
    /// node carries a representative term, the IRI in `binding`. A term-less node
    /// leaves `binding` unset, so the answer column emits as `None` / Java
    /// `null` (`m_nodesToTerms.get(node)`).
    fn bind_role_endpoint(
        v: &str,
        node: NodeId,
        node_to_representative: &HashMap<NodeId, Individual>,
        binding: &mut HashMap<String, String>,
        bound_so_far: &mut std::collections::HashSet<String>,
        node_binding: &mut HashMap<String, NodeId>,
    ) {
        node_binding.insert(v.to_string(), node);
        bound_so_far.insert(v.to_string());
        match node_to_representative.get(&node) {
            Some(representative) => {
                binding.insert(v.to_string(), representative.iri().to_string());
            }
            None => {
                binding.remove(v);
            }
        }
    }

    /// `compileHeads` / `QueryAnswerCallback`: emit exactly one answer tuple
    /// (ConjunctiveQuery.java `QueryAnswerCallback.execute`).
    ///
    /// Each answer position is the binding of the corresponding answer variable.
    /// An answer variable maps to `None` (Java's `null`) in either of the two
    /// `m_nodesToTerms.get(node)`-is-`null` cases:
    ///   * it was never bound by a concept/role retrieval (a disconnected
    ///     variable that occurs in no body atom), so its values-buffer slot is
    ///     unset and `m_nodesToTerms.get(null)` is `null`; or
    ///   * it was bound to a node that carries no term (A2), so
    ///     `m_nodesToTerms.get(node)` is `null`.
    /// In both cases the column is reported once as `None` -- the variable is NOT
    /// enumerated over the named individuals, and the row is NOT dropped. A bound
    /// variable that landed on a term-carrying node has its IRI in `binding`.
    fn emit_answers(
        &self,
        binding: &HashMap<String, String>,
        _bound_so_far: &std::collections::HashSet<String>,
        collector: &mut dyn QueryResultCollector,
    ) {
        let answer: Vec<Option<String>> = self
            .answer_terms
            .iter()
            .map(|t| match t {
                // Present in `binding` -> the bound node's representative term;
                // absent -> Java `null` (disconnected, or bound to a term-less
                // node).
                QueryTerm::Variable(v) => binding.get(v).cloned(),
                // A constant answer term echoes the constant (compileHeads leaves a
                // non-Variable answer term in place).
                QueryTerm::Individual(i) => Some(i.clone()),
            })
            .collect();
        collector.process_result(&answer);
    }
}

/// The atomic concept inside a (necessarily atomic) concept query label.
fn concept_as_atomic(concept: &Concept) -> &AtomicConcept {
    match concept {
        Concept::AtomicConcept(c) => c,
        _ => unreachable!("query concept labels are atomic concepts"),
    }
}

/// Port of `HyperresolutionManager.BodyAtomsSwapper.getSwappedDLClause`
/// (HyperresolutionManager.java:271-307) over query atoms, starting from body
/// index 0 (the query has no externally-bound delta atom, so the first atom is
/// chosen by `getAtomGoodness` like the rest -- here we seed with index 0 and
/// then greedily pick the most selective remaining atom). Queries carry no
/// `NodeIDLessEqualThan` / `NodeIDsAscendingOrEqual` atoms, so the comparison-
/// atom bookkeeping of the Java swapper collapses to the general branch of
/// `getAtomGoodness`.
fn swap_body_atoms(atoms: &[QueryAtom]) -> Vec<QueryAtom> {
    if atoms.is_empty() {
        return Vec::new();
    }
    let mut used = vec![false; atoms.len()];
    let mut reordered: Vec<QueryAtom> = Vec::new();
    let mut bound_variables: std::collections::HashSet<String> = std::collections::HashSet::new();

    // Seed with body atom 0 (ConjunctiveQuery passes bodyIndex 0 to the swapper).
    add_atom_variables(&atoms[0], &mut bound_variables);
    reordered.push(atoms[0].clone());
    used[0] = true;

    while reordered.len() != atoms.len() {
        // BodyAtomsSwapper iterates indices in reverse, keeping the first atom of
        // maximal goodness it meets (strict `>`), so on a tie the highest index wins.
        let mut best_index: Option<usize> = None;
        let mut best_goodness = -1000;
        for index in (0..atoms.len()).rev() {
            if used[index] {
                continue;
            }
            let goodness = atom_goodness(&atoms[index], &bound_variables);
            if goodness > best_goodness {
                best_goodness = goodness;
                best_index = Some(index);
            }
        }
        let best_index = best_index.expect("an unused atom remains");
        reordered.push(atoms[best_index].clone());
        used[best_index] = true;
        add_atom_variables(&atoms[best_index], &mut bound_variables);
    }
    reordered
}

/// Port of `BodyAtomsSwapper.getAtomGoodness` general branch
/// (HyperresolutionManager.java:309-360): goodness = boundVars*100 -
/// unboundVars*10 (the NodeID-comparison bonus never applies to query atoms).
fn atom_goodness(atom: &QueryAtom, bound_variables: &std::collections::HashSet<String>) -> i32 {
    let mut number_of_bound = 0;
    let mut number_of_unbound = 0;
    for term in atom.terms() {
        if let QueryTerm::Variable(v) = term {
            if bound_variables.contains(v) {
                number_of_bound += 1;
            } else {
                number_of_unbound += 1;
            }
        }
    }
    number_of_bound * 100 - number_of_unbound * 10
}

fn add_atom_variables(atom: &QueryAtom, bound_variables: &mut std::collections::HashSet<String>) {
    for term in atom.terms() {
        if let QueryTerm::Variable(v) = term {
            bound_variables.insert(v.clone());
        }
    }
}

/// The result of `DatalogEngine.materialize()`: the saturated tableau (the
/// deterministic Horn closure) plus the term->canonical-node mapping. Mirrors
/// the `m_extensionManager` / `m_termsToNodes` / `m_termsToRepresentatives`
/// state HermiT populates in `DatalogEngine.materialize` (DatalogEngine.java:48-73).
struct Materialization {
    tableau: Tableau,
    /// Each named individual term -> its canonical tableau node.
    term_to_node: HashMap<Individual, NodeId>,
    /// Port of `DatalogEngine.m_nodesToTerms` (DatalogEngine.java:30,56-57):
    /// the single `node -> term` map that BOTH the query answer path
    /// (`ConjunctiveQuery.QueryAnswerCallback`, which writes
    /// `m_nodesToTerms.get(node)` into the result buffer) and
    /// `getRepresentative` / `getEquivalenceClass` consult, so they are mutually
    /// consistent.
    ///
    /// Java fills this with `for (entry : m_termsToNodes.entrySet())
    /// m_nodesToTerms.put(entry.getValue(),entry.getKey())`. The terms map is
    /// injective on raw load nodes (each individual gets its own load node), so
    /// there are no collisions: every raw node maps back to exactly one term.
    ///
    /// Java keys `m_nodesToTerms` by `entry.getValue()` (the term's RAW loaded
    /// node) and then always reads it through `node.getCanonicalNode()`. The port
    /// keys by the same raw load node and every lookup canonicalizes before
    /// indexing (`get(canonical)`), so the representative of a merged class is the
    /// term whose raw node IS the merge survivor -- matching Java's
    /// `m_nodesToTerms.get(node.getCanonicalNode())`: the query path binds
    /// canonical nodes, and `getRepresentative` / `getEquivalenceClass`
    /// canonicalize before looking up. A canonical node carrying a loaded term
    /// hits; otherwise the lookup is `None` (Java's `null`).
    node_to_term: HashMap<NodeId, Individual>,
}

impl Materialization {
    /// The canonical node for the individual named `iri`, if it was loaded.
    fn node_for_iri(&self, iri: &str) -> Option<NodeId> {
        self.term_to_node
            .get(&Individual::create(iri))
            .map(|&node| self.tableau.get_canonical_node(node))
    }

    /// `getRepresentative`: the canonical term of `individual`'s equivalence class,
    /// i.e. the individual whose loaded node is the canonical (merge-survivor) node
    /// shared by the class. `None` when `individual` was not loaded, or when the
    /// canonical node carries no individual term (matching Java's `nodesToTerms`
    /// returning `null`).
    fn representative_of(&self, individual: &Individual) -> Option<Individual> {
        let &node = self.term_to_node.get(individual)?;
        let canonical = self.tableau.get_canonical_node(node);
        // `m_termsToRepresentatives.get(term)` == `m_nodesToTerms.get(canonical)`
        // (DatalogEngine.java:60-69): read the representative from the single
        // precomputed `node -> term` map, so this agrees with the query path.
        // `None` when the canonical node carries no loaded term (Java `null`).
        self.node_to_term.get(&canonical).cloned()
    }

    /// `getEquivalenceClass`: every loaded individual whose canonical node is the
    /// same as `individual`'s (the merged-together same-as group). Empty when
    /// `individual` was not loaded.
    fn equivalence_class_of(&self, individual: &Individual) -> std::collections::HashSet<Individual> {
        let Some(&node) = self.term_to_node.get(individual) else {
            return std::collections::HashSet::new();
        };
        let canonical = self.tableau.get_canonical_node(node);
        self.term_to_node
            .iter()
            .filter(|&(_, &n)| self.tableau.get_canonical_node(n) == canonical)
            .map(|(i, _)| i.clone())
            .collect()
    }

    /// The canonical nodes carrying `concept` in the materialized model, paired
    /// with the node id again (so the caller can read it). This is the
    /// concept-atom retrieval used to bind an unbound query variable to actual
    /// successors -- the table-driven binding of
    /// `DLClauseEvaluator.ConjunctionCompiler.compileBodyAtom` for a unary atom,
    /// over the binary (concept) extension table.
    fn concept_extension(&self, concept: &Concept) -> Vec<(NodeId, NodeId)> {
        use crate::tableau::extension_table::View;
        // owl:Thing has a binary-table tuple stored on every abstract node
        // (Tableau.java:662-663 `addConceptAssertion(THING,node)` on node
        // creation), so a query retrieval over the THING extension returns every
        // active abstract node -- including any abstract node that carries no
        // loaded term. The port does not physically store the THING tuples, so
        // enumerate the active abstract tableau nodes directly, mirroring that
        // retrieval (active-filtered, deduped by canonical node). For any other
        // atomic concept, scan its binary-table extension.
        if matches!(concept, Concept::AtomicConcept(c) if c == AtomicConcept::thing()) {
            let mut seen = std::collections::HashSet::new();
            let mut result = Vec::new();
            let mut node = self.tableau.get_first_tableau_node();
            while let Some(id) = node {
                let n = self.tableau.node(id);
                if n.is_active() && n.get_node_type().is_abstract() {
                    let canonical = self.tableau.get_canonical_node(id);
                    if seen.insert(canonical) {
                        result.push((canonical, canonical));
                    }
                }
                node = self.tableau.node(id).next_tableau_node;
            }
            return result;
        }
        let label = TableauObject::Concept(concept.clone());
        let retrieval = self.tableau.create_binary_retrieval(
            [0, -1],
            [Some(label), None],
            View::Total,
        );
        let mut result = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            let node = self
                .tableau
                .binary_extension_table
                .get_tuple_object(tuple_index, 1)
                .as_node()
                .unwrap();
            let canonical = self.tableau.get_canonical_node(node);
            result.push((canonical, canonical));
        }
        result
    }

    /// The `(from, to)` canonical-node pairs of `role`'s extension in the
    /// materialized model -- the binary-atom retrieval used to bind unbound role
    /// variables to actual successors (over the ternary extension table). An
    /// inverse role reads the underlying atomic role's tuples with the endpoints
    /// swapped (mirroring `contains_role_assertion`).
    fn role_extension(&self, role: &Role) -> Vec<(NodeId, NodeId)> {
        use crate::tableau::extension_table::View;
        let (atomic_role, swap) = match role {
            Role::AtomicRole(r) => (r.clone(), false),
            Role::InverseRole(r) => (r.get_inverse_of().clone(), true),
        };
        let label = TableauObject::DLPredicate(DLPredicate::AtomicRole(atomic_role));
        let retrieval = self.tableau.create_ternary_retrieval(
            [0, -1, -1],
            [Some(label), None, None],
            View::Total,
        );
        let mut result = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            let a = self
                .tableau
                .ternary_extension_table
                .get_tuple_object(tuple_index, 1)
                .as_node()
                .unwrap();
            let b = self
                .tableau
                .ternary_extension_table
                .get_tuple_object(tuple_index, 2)
                .as_node()
                .unwrap();
            let a = self.tableau.get_canonical_node(a);
            let b = self.tableau.get_canonical_node(b);
            if swap {
                result.push((b, a));
            } else {
                result.push((a, b));
            }
        }
        result
    }

    /// Whether `concept(node)` holds in the materialized model: the atomic
    /// concept is asserted on the given (canonical) node.
    fn concept_holds_node(&self, concept: &AtomicConcept, node: NodeId) -> bool {
        self.tableau
            .contains_concept_assertion(&Concept::AtomicConcept(concept.clone()), node)
    }

    /// Whether `role(from_node,to_node)` holds in the materialized model -- the
    /// fully-bound role-atom containment check.
    fn role_holds_nodes(&self, role: &Role, from_node: NodeId, to_node: NodeId) -> bool {
        self.tableau.contains_role_assertion(role, from_node, to_node)
    }

    /// The `(t1, t2)` canonical-node pairs of a comparison `predicate`'s
    /// (`Equality` / `Inequality`) extension in the materialized model -- the
    /// ternary retrieval HermiT's `DLClauseEvaluator` compiles for a comparison
    /// body atom (it is NOT special-cased). `Equality` assertions merge nodes
    /// rather than being stored, so the `Equality` extension is empty; `Inequality`
    /// assertions are stored (in the asserted direction).
    fn comparison_extension(&self, predicate: DLPredicate) -> Vec<(NodeId, NodeId)> {
        use crate::tableau::extension_table::View;
        let label = TableauObject::DLPredicate(predicate);
        let retrieval = self.tableau.create_ternary_retrieval(
            [0, -1, -1],
            [Some(label), None, None],
            View::Total,
        );
        let mut result = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            let a = self
                .tableau
                .ternary_extension_table
                .get_tuple_object(tuple_index, 1)
                .as_node()
                .unwrap();
            let b = self
                .tableau
                .ternary_extension_table
                .get_tuple_object(tuple_index, 2)
                .as_node()
                .unwrap();
            result.push((self.tableau.get_canonical_node(a), self.tableau.get_canonical_node(b)));
        }
        result
    }

    /// Whether a comparison `predicate`(n0, n1) tuple is present in the materialized
    /// model -- the fully-bound ternary retrieval (`ExtensionManager.containsAssertion`).
    /// Directional, matching Java's single-orientation `containsAssertion`.
    fn comparison_holds_nodes(&self, predicate: DLPredicate, n0: NodeId, n1: NodeId) -> bool {
        use crate::tableau::extension_table::View;
        let label = TableauObject::DLPredicate(predicate);
        let retrieval = self.tableau.create_ternary_retrieval(
            [0, 1, 2],
            [Some(label), Some(TableauObject::Node(n0)), Some(TableauObject::Node(n1))],
            View::Total,
        );
        !retrieval.after_last()
    }
}

/// Port of `DatalogEngine`: a materializing engine over a clausified
/// `DLOntology`. Built from a `SetOntology` via the port's clausification
/// front-end, it rejects disjunctive-head ontologies at construction
/// (DatalogEngine.java:34-37) and answers DL-safe conjunctive queries off the
/// deterministic Horn materialization.
pub struct DatalogEngine {
    dl_ontology: DLOntology,
    /// The named individuals (IRIs) over which DL-safe query variables range.
    individuals: Vec<String>,
    /// The materialized deterministic Horn closure, computed once and reused
    /// across queries (`DatalogEngine.materialize`'s `if (m_extensionManager==null)`
    /// idempotent cache). Populated on the first successful `materialize()`.
    materialization: std::cell::RefCell<Option<std::rc::Rc<Materialization>>>,
    /// Shared interrupt latch (DatalogEngine.java:26,38: `m_interruptFlag`).
    /// Created once with no timeout (matching `new InterruptFlag(0)`) and
    /// injected into every `Tableau` built by `materialize()` so the
    /// saturation loop can be cancelled cooperatively via `interrupt()`.
    interrupt_handle: crate::tableau::interrupt_flag::InterruptHandle,
}

impl DatalogEngine {
    /// Builds an engine over `ontology`.
    ///
    /// Faithful to `DatalogEngine(DLOntology)` (DatalogEngine.java:34-44): the
    /// `SetOntology` is first run through the port's clausification front-end
    /// (normalize -> built-in properties -> object-property inclusions ->
    /// clausify, the same pipeline `reasoner::clausify_for_query` uses), then
    /// every resulting DL-clause is checked: a clause with head length > 1
    /// (a disjunctive head) makes the engine inapplicable, so we return `Err`
    /// (Java throws `IllegalArgumentException("...rules with disjunctive
    /// heads.")`).
    pub fn new(ontology: &SetOntology<A>) -> Result<DatalogEngine, String> {
        let dl_ontology = clausify(ontology)?;

        // DatalogEngine.java:35-37: reject disjunctive heads.
        for clause in dl_ontology.get_dl_clauses() {
            if clause.get_head_length() > 1 {
                return Err(
                    "The supplied DL ontology contains rules with disjunctive heads.".to_string(),
                );
            }
        }

        // Java's m_nodesToTerms is populated only via getNodeForTerm inside
        // loadPositiveFact / loadNegativeFact, so a declared-but-factless
        // individual gets NO node and cannot be a query answer. Anonymous
        // individuals that appear in facts DO get an NI node and ARE in
        // m_nodesToTerms (Tableau.java:355-356), so they are valid answers.
        // Mirror both behaviours: collect IRIs from positive + negative facts
        // only, including anonymous individuals.
        // (DatalogEngine.java:48-73; Tableau.java:350-371)
        let mut individuals: Vec<String> = Vec::new();
        for atom in dl_ontology.get_positive_facts().iter().chain(dl_ontology.get_negative_facts()) {
            for i in 0..atom.get_arity() {
                if let Term::Individual(individual) = atom.get_argument(i) {
                    let iri = individual.iri().to_string();
                    if !individuals.contains(&iri) {
                        individuals.push(iri);
                    }
                }
            }
        }

        // DatalogEngine.java:38: `m_interruptFlag = new InterruptFlag(0)` —
        // timeout=0 means no timer, pure cooperative cancellation via interrupt().
        let interrupt_handle = crate::tableau::interrupt_flag::InterruptFlag::new(0).interrupt_handle();
        Ok(DatalogEngine {
            dl_ontology,
            individuals,
            interrupt_handle,
            materialization: std::cell::RefCell::new(None),
        })
    }

    pub fn individuals(&self) -> &[String] {
        &self.individuals
    }

    /// Latches the interrupt flag so the next (or current) `materialize()` call
    /// aborts its saturation loop early (DatalogEngine.java:45-47: `interrupt()`).
    /// Has no effect on the correctness of a completed query; only cooperative
    /// cancellation of a long-running materialization is provided.
    pub fn interrupt(&self) {
        self.interrupt_handle.interrupt();
    }

    /// Port of `DatalogEngine.materialize()` (DatalogEngine.java:48-73).
    ///
    /// Builds a single tableau with the *null existential strategy* (no
    /// existential expansion), loads the ABox, saturates the deterministic Horn
    /// closure, and records the term->node mapping. Returns the materialized
    /// state, or `Err` on a clash (the ontology is unsatisfiable -- Java's
    /// `materialize()` returns `false`, and `ConjunctiveQuery`'s constructor then
    /// throws `IllegalStateException("...unsatisfiable.")`).
    ///
    /// Design note: HermiT materializes once and caches the `ExtensionManager`;
    /// the `Tableau` is not cheaply `Clone`-able, so this port materializes on
    /// demand per `evaluate` call. The answers are identical -- the same single
    /// saturated Horn model is read off either way -- only the caching is dropped.
    /// The disjunctive-head rejection and the materialize-once-per-evaluation
    /// (not per-binding-entailment) model are preserved.
    /// `getRepresentative(term)`: the canonical representative of `individual`'s
    /// same-as equivalence class in the materialized model. Materializes the engine
    /// on first use (`Err` if the ontology is unsatisfiable).
    pub fn get_representative(&self, individual: &Individual) -> Result<Option<Individual>, String> {
        Ok(self.materialize()?.representative_of(individual))
    }

    /// `getEquivalenceClass(term)`: every individual merged same-as with
    /// `individual` in the materialized model. Materializes on first use.
    pub fn get_equivalence_class(
        &self,
        individual: &Individual,
    ) -> Result<std::collections::HashSet<Individual>, String> {
        Ok(self.materialize()?.equivalence_class_of(individual))
    }

    fn materialize(&self) -> Result<std::rc::Rc<Materialization>, String> {
        // Idempotent cache (DatalogEngine.java:49 `if (m_extensionManager==null)`):
        // a successful materialization is reused by every later query.
        if let Some(cached) = self.materialization.borrow().as_ref() {
            return Ok(std::rc::Rc::clone(cached));
        }
        let mut tableau = Tableau::new();
        // DatalogEngine.java:54: the shared `m_interruptFlag` is passed into
        // the Tableau constructor so the saturation loop can be cancelled.
        tableau.interrupt_flag =
            crate::tableau::interrupt_flag::InterruptFlag::from_handle(&self.interrupt_handle);
        let mut manager = HyperresolutionManager::new(self.dl_ontology.get_dl_clauses());
        tableau.update_extension_flags(&manager);
        tableau.check_datatypes = self.dl_ontology.has_datatypes();

        let term_to_node = self.load_abox(&mut tableau);

        if !tableau.contains_clash() {
            // Saturate the deterministic Horn closure. With the null existential
            // strategy we never expand existentials; a Horn (non-disjunctive)
            // ontology has no ground disjunctions, so saturation is just the
            // hyperresolution + datatype fixpoint (DatalogEngine.materialize's
            // `tableau.isSatisfiable` with `NullExistentialExpansionStrategy`).
            self.saturate(&mut tableau, &mut manager);
        }

        if tableau.contains_clash() {
            return Err("The supplied DL ontology is unsatisfiable.".to_string());
        }

        // DatalogEngine.java:56-57: build `m_nodesToTerms` ONCE from the terms
        // map: `for (entry : m_termsToNodes.entrySet())
        // m_nodesToTerms.put(entry.getValue(),entry.getKey())`. The map is keyed by
        // each term's RAW load node (term_to_node is injective, so there are no
        // collisions). The representative of a merged class is then
        // `m_nodesToTerms.get(node.getCanonicalNode())` (DatalogEngine.java:62) --
        // i.e. the term whose raw node IS the merge survivor, which is
        // deterministic. Keying by the canonical node instead would make the
        // representative an arbitrary class member (last writer over the iteration);
        // every lookup (`representative_of`, the answer path) already canonicalizes
        // the bound node before indexing, so keying by the raw node reproduces
        // Java exactly.
        let mut node_to_term: HashMap<NodeId, Individual> = HashMap::new();
        for (individual, &node) in &term_to_node {
            node_to_term.insert(node, individual.clone());
        }

        let materialization =
            std::rc::Rc::new(Materialization { tableau, term_to_node, node_to_term });
        *self.materialization.borrow_mut() = Some(std::rc::Rc::clone(&materialization));
        Ok(materialization)
    }

    /// Saturates the tableau under hyperresolution + datatype checking, WITHOUT
    /// existential expansion or disjunction branching (the null existential
    /// strategy). This is the deterministic Horn closure of HermiT's
    /// `doIteration` loop restricted to the rule-application fixpoint.
    fn saturate(&self, tableau: &mut Tableau, manager: &mut HyperresolutionManager) {
        // runCalculus (Tableau.java:380, 405): bracket the saturation loop with
        // startTask/endTask so that an interrupt latched *before* this run is
        // cleared (startTask resets the flag) and only an interrupt arriving
        // during the run aborts it.
        tableau.start_task();
        loop {
            // DatalogEngine.java / Tableau.doIteration: poll the interrupt flag
            // at the head of every iteration so a cooperative cancel is honoured
            // promptly (matching `m_interruptFlag.checkInterrupt()`).
            if tableau.check_interrupt().is_err() {
                break;
            }
            if tableau.contains_clash() {
                break;
            }
            // Tableau.doIteration line 412: drain buffered annotated equalities
            // (the deferred nominal-introduction rule) before the propagate loop.
            tableau.process_annotated_equalities();
            let mut has_change = false;
            while tableau.propagate_delta_new_all() && !tableau.contains_clash() {
                // Tableau.doIteration line 415-416: description-graph constraints
                // (a no-op when the ontology has no description graphs).
                if !tableau.contains_clash() {
                    tableau.check_graph_constraints();
                }
                manager.apply_dl_clauses(tableau);
                // Tableau.java:421-422: `if (m_checkUnknownDatatypeRestrictions &&
                // !containsClash()) applyUnknownDatatypeRestrictionSemantics();`
                if tableau.check_unknown_datatype_restrictions && !tableau.contains_clash() {
                    tableau.apply_unknown_datatype_restriction_semantics();
                }
                // Tableau.java:423-424: `if (m_checkDatatypes && !containsClash()) checkDatatypeConstraints();`
                if tableau.check_datatypes && !tableau.contains_clash() {
                    tableau.check_datatype_constraints();
                }
                // Tableau.doIteration line 426: drain buffered annotated
                // equalities after the round's deterministic saturation.
                if !tableau.contains_clash() {
                    tableau.process_annotated_equalities();
                }
                has_change = true;
            }
            if !has_change {
                break;
            }
        }
        tableau.end_task();
    }

    /// Loads the clausified ABox into `tableau` (a named node per individual,
    /// then the positive and negative facts), returning the term->node mapping.
    /// Mirrors `Reasoner.load_abox` / Java's ABox loading, restricted to the
    /// facts the datalog engine materializes.
    fn load_abox(&self, tableau: &mut Tableau) -> HashMap<Individual, NodeId> {
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let mut nodes_for_terms: HashMap<Term, NodeId> = HashMap::new();

        // Tableau.loadPermanentABox (Tableau.java:269-274): a tableau node is
        // created lazily (via getNodeForTerm) only for terms that occur in the
        // positive/negative facts. Declared-but-factless individuals get no node.
        let mut clashed = false;
        for atom in self.dl_ontology.get_positive_facts() {
            self.assert_fact(tableau, atom, &mut nodes_for_terms, &empty, false);
            if tableau.contains_clash() {
                clashed = true;
                break;
            }
        }
        if !clashed {
            for atom in self.dl_ontology.get_negative_facts() {
                self.assert_fact(tableau, atom, &mut nodes_for_terms, &empty, true);
                if tableau.contains_clash() {
                    break;
                }
            }
        }

        // Ensure at least one node exists so a TBox-only inconsistency (e.g.
        // `⊤ ⊑ ⊥`) is detected (cf. Tableau.java:307-309).
        if tableau.get_first_tableau_node().is_none() {
            tableau.create_new_ni_node(&empty);
        }

        // term->node mapping for query answering, restricted to the individuals
        // that occur in facts (mirrors Java's m_termsToNodes population).
        let mut term_to_node: HashMap<Individual, NodeId> = HashMap::new();
        for (term, node) in &nodes_for_terms {
            if let Term::Individual(individual) = term {
                term_to_node.insert(individual.clone(), *node);
            }
        }

        term_to_node
    }

    fn node_for_term(
        &self,
        tableau: &mut Tableau,
        term: &Term,
        nodes_for_terms: &mut HashMap<Term, NodeId>,
        empty: &DependencySet,
    ) -> NodeId {
        let raw = if let Some(&node) = nodes_for_terms.get(term) {
            node
        } else {
            let node = match term {
                Term::Constant(constant) => {
                    let node = tableau.create_new_root_constant_node(empty);
                    tableau.node_mut(node).constant_value = Some(constant.clone());
                    // Tableau.getNodeForTerm (Tableau.java:363-366): anonymous
                    // constant values are deliberately NOT pinned to a particular
                    // value, so no ConstantEnumeration is asserted for them.
                    if !constant.is_anonymous() {
                        let enumeration =
                            crate::model::ConstantEnumeration::create(vec![constant.clone()]);
                        tableau.add_dl_predicate_assertion(
                            DLPredicate::ConstantEnumeration(enumeration),
                            node,
                            empty,
                            true,
                        );
                    }
                    node
                }
                // Tableau.getNodeForTerm (Tableau.java:353-358): anonymous
                // individuals get an NI node; named individuals get a named node.
                Term::Individual(individual) if individual.is_anonymous() => {
                    tableau.create_new_ni_node(empty)
                }
                _ => tableau.create_new_named_node(empty),
            };
            nodes_for_terms.insert(term.clone(), node);
            node
        };
        tableau.get_canonical_node(raw)
    }

    fn assert_fact(
        &self,
        tableau: &mut Tableau,
        atom: &crate::model::Atom,
        nodes_for_terms: &mut HashMap<Term, NodeId>,
        empty: &DependencySet,
        negative: bool,
    ) {
        let predicate = atom.get_dl_predicate().clone();
        match atom.get_arity() {
            1 => {
                let node =
                    self.node_for_term(tableau, atom.get_argument(0), nodes_for_terms, empty);
                if negative {
                    if let DLPredicate::AtomicConcept(a) = predicate {
                        tableau.add_concept_assertion(
                            Concept::from(a.get_negation()),
                            node,
                            empty,
                            true,
                        );
                    }
                } else {
                    tableau.add_unary_from_predicate(predicate, node, empty, true);
                }
            }
            2 => {
                let n0 =
                    self.node_for_term(tableau, atom.get_argument(0), nodes_for_terms, empty);
                let n1 =
                    self.node_for_term(tableau, atom.get_argument(1), nodes_for_terms, empty);
                match predicate {
                    DLPredicate::AtomicRole(r) => {
                        if negative {
                            tableau.add_ternary(
                                TableauObject::NegatedAtomicRole(
                                    crate::model::NegatedAtomicRole::create(r),
                                ),
                                n0,
                                n1,
                                empty,
                                true,
                            );
                        } else {
                            tableau.add_role_assertion(Role::AtomicRole(r), n0, n1, empty, true);
                        }
                    }
                    DLPredicate::Equality => {
                        // loadNegativeFact (Tableau.java:343-344): a negative
                        // Equality fact asserts Inequality; a positive one merges.
                        if negative {
                            tableau.add_ternary(
                                TableauObject::DLPredicate(DLPredicate::Inequality),
                                n0,
                                n1,
                                empty,
                                true,
                            );
                        } else {
                            tableau.merge_nodes(n0, n1, empty);
                        }
                    }
                    DLPredicate::Inequality => {
                        // loadNegativeFact (Tableau.java:345-346): a negative
                        // Inequality fact asserts Equality (merge); a positive one
                        // asserts Inequality.
                        if negative {
                            tableau.merge_nodes(n0, n1, empty);
                        } else {
                            tableau.add_ternary(
                                TableauObject::DLPredicate(DLPredicate::Inequality),
                                n0,
                                n1,
                                empty,
                                true,
                            );
                        }
                    }
                    other => {
                        tableau.add_ternary(
                            TableauObject::DLPredicate(other),
                            n0,
                            n1,
                            empty,
                            true,
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

/// Runs the port's clausification front-end (normalize -> built-in properties ->
/// object-property inclusions -> clausify) over a `SetOntology`, producing the
/// `DLOntology` the engine is built over. Mirrors
/// `reasoner::clausify_for_query` (the same pipeline HermiT runs before building
/// a `DatalogEngine` over the resulting `DLOntology`).
fn clausify(ontology: &SetOntology<A>) -> Result<DLOntology, String> {
    use crate::structural::{
        BuiltInPropertyManager, Configuration, OWLAxioms, OWLAxiomsExpressivity, OWLClausification,
        OWLNormalization, ObjectPropertyInclusionManager,
    };
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology)?;
    let definitions_count = normalization.definitions_count();
    let mut axioms = normalization.into_axioms();
    BuiltInPropertyManager::new().axiomatize_built_in_properties_as_needed(&mut axioms);
    // preprocessAndClausify runs the object-property inclusion manager
    // unconditionally (it builds the automata and rewrites in every case).
    let manager = ObjectPropertyInclusionManager::new(&mut axioms)?;
    manager.rewrite_negative_object_property_assertions(&mut axioms, definitions_count);
    manager.rewrite_axioms(&mut axioms, 0)?;
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    OWLClausification::new(Configuration::default()).clausify(
        "http://hermit-rs/anonymous-ontology",
        &axioms,
        &expressivity,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use horned_owl::model::{
        Build, ClassAssertion, Component, DisjointClasses, Individual as OwlInd, MutableOntology,
        ObjectPropertyAssertion, SubClassOf,
    };

    fn person_ontology() -> (SetOntology<A>, Build<A>) {
        let build = Build::new_arc();
        let person = build.class("http://example.org/Person");
        let knows = build.object_property("http://example.org/knows");
        let alice = build.named_individual("http://example.org/alice");
        let bob = build.named_individual("http://example.org/bob");
        let student = build.class("http://example.org/Student");
        let knows_e = OPE::ObjectProperty(knows.clone());

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(person.clone()),
            i: OwlInd::Named(alice.clone()),
        }));
        ontology.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(student.clone()),
            sup: CE::Class(person.clone()),
        }));
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(student.clone()),
            i: OwlInd::Named(bob.clone()),
        }));
        ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope: knows_e,
            from: OwlInd::Named(alice),
            to: OwlInd::Named(bob),
        }));
        (ontology, build)
    }

    #[test]
    fn horn_query_certain_answers_off_materialization() {
        let (ontology, build) = person_ontology();
        let person = build.class("http://example.org/Person");
        let knows = build.object_property("http://example.org/knows");
        let knows_e = OPE::ObjectProperty(knows);

        let engine = DatalogEngine::new(&ontology).expect("Horn ontology builds an engine");

        // Q(x) :- Person(x): both alice and bob (bob a Person via subclass), read
        // off the materialized Horn model.
        let query = ConjunctiveQuery::new(
            vec![QueryAtom::Concept(CE::Class(person.clone()), QueryTerm::Variable("x".into()))],
            vec![QueryTerm::Variable("x".into())],
        );
        let mut answers: Vec<Vec<String>> = Vec::new();
        query.evaluate(&engine, &mut answers).unwrap();
        let mut flat: Vec<String> = answers.iter().map(|a| a[0].clone()).collect();
        flat.sort();
        assert_eq!(flat, vec!["http://example.org/alice", "http://example.org/bob"]);

        // Q(x) :- knows(x, y), Person(y): alice (knows bob, a Person).
        let query2 = ConjunctiveQuery::new(
            vec![
                QueryAtom::Role(
                    knows_e,
                    QueryTerm::Variable("x".into()),
                    QueryTerm::Variable("y".into()),
                ),
                QueryAtom::Concept(CE::Class(person), QueryTerm::Variable("y".into())),
            ],
            vec![QueryTerm::Variable("x".into())],
        );
        let mut answers2: Vec<Vec<String>> = Vec::new();
        query2.evaluate(&engine, &mut answers2).unwrap();
        assert_eq!(answers2, vec![vec!["http://example.org/alice".to_string()]]);
    }

    #[test]
    fn disjunctive_head_ontology_rejected_at_construction() {
        // C ⊑ A ⊔ B clausifies to a clause with a disjunctive head (head length
        // 2). DatalogEngine.java:35-37 rejects this in the constructor.
        let build = Build::new_arc();
        let a = build.class("http://example.org/A");
        let b = build.class("http://example.org/B");
        let c = build.class("http://example.org/C");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::SubClassOf(SubClassOf {
            sub: CE::Class(c),
            sup: CE::ObjectUnionOf(vec![CE::Class(a), CE::Class(b)]),
        }));
        // Force the disjunction to matter by asserting C on an individual.
        let x = build.named_individual("http://example.org/x");
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(build.class("http://example.org/C")),
            i: OwlInd::Named(x),
        }));

        let result = DatalogEngine::new(&ontology);
        assert!(result.is_err(), "an ontology with a disjunctive head must be rejected");
        assert!(result.err().unwrap().contains("disjunctive heads"));
    }

    #[test]
    fn inconsistent_ontology_errors_at_materialization() {
        // An unsatisfiable ontology makes materialize() clash; the query
        // errors rather than returning the full cross-product of individuals.
        let build = Build::new_arc();
        let a = build.class("http://example.org/A");
        let b = build.class("http://example.org/B");
        let person = build.class("http://example.org/Person");
        let x = build.named_individual("http://example.org/x");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::DisjointClasses(DisjointClasses(vec![
            CE::Class(a.clone()),
            CE::Class(b.clone()),
        ])));
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(a),
            i: OwlInd::Named(x.clone()),
        }));
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(b),
            i: OwlInd::Named(x),
        }));

        // Disjointness clausifies to A ⊓ B ⊑ ⊥, a Horn clause (empty/⊥ head), so
        // the engine builds; the inconsistency surfaces at materialization.
        let engine = DatalogEngine::new(&ontology).expect("disjointness is Horn");
        let query = ConjunctiveQuery::new(
            vec![QueryAtom::Concept(CE::Class(person), QueryTerm::Variable("x".into()))],
            vec![QueryTerm::Variable("x".into())],
        );
        let mut answers: Vec<Vec<String>> = Vec::new();
        let result = query.evaluate(&engine, &mut answers);
        assert!(result.is_err(), "querying an inconsistent ontology must error, not return tuples");
        assert!(answers.is_empty());
    }

    #[test]
    fn equality_atom_off_materialization() {
        // HermiT compiles an Equality query atom as a retrieval over the Equality
        // extension table (DLClauseEvaluator), but Equality assertions merge nodes
        // and are never stored, so that extension is always empty: a query body
        // containing an Equality atom therefore yields NO answers -- regardless of
        // whether the two individuals are actually the same (a == b) or distinct
        // (a == c). We follow that implementation rather than computing the OWL
        // answer by a different (node-identity) mechanism.
        let build = Build::new_arc();
        let a = build.named_individual("http://example.org/a");
        let b = build.named_individual("http://example.org/b");
        let c = build.named_individual("http://example.org/c");
        use horned_owl::model::SameIndividual;

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::SameIndividual(SameIndividual(vec![
            OwlInd::Named(a.clone()),
            OwlInd::Named(b.clone()),
        ])));
        ontology.insert(Component::DeclareNamedIndividual(
            horned_owl::model::DeclareNamedIndividual(c.clone()),
        ));

        let engine = DatalogEngine::new(&ontology).expect("Horn ontology");

        let eq_query = ConjunctiveQuery::new(
            vec![QueryAtom::Equality(
                QueryTerm::Individual("http://example.org/a".into()),
                QueryTerm::Individual("http://example.org/b".into()),
            )],
            vec![],
        );
        let mut eq_answers: Vec<Vec<String>> = Vec::new();
        eq_query.evaluate(&engine, &mut eq_answers).unwrap();
        assert!(
            eq_answers.is_empty(),
            "Equality extension is empty (merges, never stored), so HermiT yields no answer"
        );

        // `c` is declared but appears in no ABox fact, so it has no node in the
        // materialized model: HermiT's ValuesBufferManager rejects such a query
        // constant with "Term '...' is unknown to the reasoner."
        let neq_query = ConjunctiveQuery::new(
            vec![QueryAtom::Equality(
                QueryTerm::Individual("http://example.org/a".into()),
                QueryTerm::Individual("http://example.org/c".into()),
            )],
            vec![],
        );
        let mut neq_answers: Vec<Vec<String>> = Vec::new();
        let err = neq_query.evaluate(&engine, &mut neq_answers).unwrap_err();
        assert!(err.contains("unknown to the reasoner"), "unexpected error: {err}");
    }

    #[test]
    fn disconnected_answer_variable_emitted_once_as_unbound() {
        // Q(x, y) :- Person(x). `y` occurs in no body atom, so Java leaves its
        // values-buffer slot unset and `m_nodesToTerms.get(null)` is null: exactly
        // one row per binding of `x`, with `y` reported as null (here `None`).
        // It must NOT be enumerated over the named individuals.
        let (ontology, build) = person_ontology();
        let person = build.class("http://example.org/Person");
        let engine = DatalogEngine::new(&ontology).expect("Horn ontology builds an engine");

        let query = ConjunctiveQuery::new(
            vec![QueryAtom::Concept(
                CE::Class(person),
                QueryTerm::Variable("x".into()),
            )],
            vec![QueryTerm::Variable("x".into()), QueryTerm::Variable("y".into())],
        );
        let mut answers: Vec<Vec<Option<String>>> = Vec::new();
        query.evaluate(&engine, &mut answers).unwrap();

        // alice and bob both satisfy Person(x); each yields ONE row, y unbound.
        assert_eq!(answers.len(), 2, "one row per Person binding, no y-enumeration");
        let mut xs: Vec<String> = answers
            .iter()
            .map(|row| {
                assert_eq!(row[1], None, "the disconnected answer variable is unbound (null)");
                row[0].clone().expect("x is bound by Person(x)")
            })
            .collect();
        xs.sort();
        assert_eq!(xs, vec!["http://example.org/alice", "http://example.org/bob"]);
    }
}
