# Querying object-property instances

For a sweep over many properties, build one `ObjectPropertyInstanceIndex` and
reuse it. The stateless `object_property_instances(ontology, property)` function
remains available for individual queries; repeated calls to that function each
construct their own index.

```rust
use hermit_rs::reasoner::ObjectPropertyInstanceIndex;
use horned_owl::model::ObjectPropertyExpression;

// `ontology` contains the ontology and its resolved import closure.
let mut index = ObjectPropertyInstanceIndex::new(&ontology)?;
for property in index.object_properties() {
    let pairs = index.object_property_instances(
        ObjectPropertyExpression::ObjectProperty(property),
    )?;
    // Each (subject, object) is an entailed pair of named individuals.
    // Use these pairs to construct inferred ObjectPropertyAssertion axioms.
}
```

Construction first saturates the original ontology, which also checks
consistency. Simple roles are read from the ternary extension table. Complex
roles use fresh source/target concepts and universal restrictions, preserving
transitivity and property-chain consequences.

The complex-role read-off uses Java's permanent role automata, compiled ontology,
and individual-aligned batches of at most 10,000 added axioms (finishing an
individual can exceed that threshold). Only the added axioms are clausified and
compiled for each batch. The preliminary model limits markers to named subjects
with an appropriate outgoing or inverse edge. The automata are also restricted
to labels that the permanent DL program can generate, including facts,
existentials, reflexivity, self restrictions, inverses and rule heads. This is an
over-approximation: concept guards and every disjunctive head remain possible.
Only fresh read-off automata are restricted; original ontology constraints are
unchanged. Blocking of a named subject triggers a conservative fallback.

These are optimizations beyond Java's unfiltered cross product, preserving the
entailed answers. Empty roles remain queryable. A sweep with no relevant complex
paths needs one saturation; otherwise it needs the preliminary model plus the
retained marker batches, shared across all properties.

Queries return known pairs directly and run entailment checks only for the
queried role's possible pairs. Positive and negative decisions are cached.
Inverse queries reuse those decisions with swapped endpoints. Top and bottom
retain their built-in meanings; anonymous individuals are excluded from results.

The index owns an immutable ontology snapshot. Use
`ObjectPropertyInstanceIndex::with_configuration` for an explicit reasoner
configuration. Interruptions are errors, rather than inconsistency verdicts.

For changing ontologies, `IncrementalReasoner::object_property_instances` creates
and reuses the same kind of index internally. Buffered changes take effect on
`flush`; non-buffered changes invalidate the index immediately.
`precompute(&[InferenceType::ObjectPropertyAssertions])` builds the shared index
and resolves all roles' possible pairs, so later queries reuse completed results.

The sparse regression checks 111 properties and 331 individuals: one
saturation for simple roles, or two for the mixed case with only six retained
markers. Another regression bounds marker clauses in the presence of 200 dormant
chains. Tests cover batching, equality aliases, inverses, anonymous paths,
existentially generated edges, reflexivity, uncertainty and cache invalidation.

An intentional correction to Java is covered by a final-batch regression:
Java's `InstanceManager` marks initialization complete at `length - 1`, skipping
a remaining individual. With 70 individuals in a transitive ring and 73 complex
roles, Java returned 4,831 pairs instead of 4,900. Rust processes the final batch
and returns all 4,900. This is a genuine Java bug, not a behavior to reproduce.

See [issue #56 measurements](issue-56-performance.md) for the cohort benchmark
and a reproducible profiling command.
