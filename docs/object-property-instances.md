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

Construction performs one saturation. Simple roles are read from the ternary
extension table. Complex roles use fresh source/target concepts and universal
restrictions for all relevant roles in the same augmented model, preserving
transitivity and property-chain consequences. That saturation also checks
consistency; there is no separate consistency saturation per property.

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

The issue #55 regression checks a synthetic ontology with 111 properties and 331
individuals and asserts **one actual saturation** across the whole sweep, with
and without multiple complex roles. Other tests compare results against
independent negative-assertion entailment checks, including nondeterministic
choices, equality aliases, inverses, and chains. The cohort ontology described
in the issue was not attached, so its wall-clock improvement was not measured.
