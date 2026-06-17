# Role-automaton inverse+chain divergence on `efo_big` — investigation & fix

Follow-up to `ROLE_AUTOMATON_ORDER_SENSITIVITY.md`. That note fixed the
*non-determinism* (the construction is now deterministic). This note tracked down
the residual divergence from ROBOT/HermiT on EFO STAR modules and **fixed it**.

## TL;DR

The EFO `MONDO_* ⊑ EFO_0000524` subsumptions that this divergence surfaced are
**not spurious — they are valid entailments**. The bug was a *completeness* bug
in hermit-rs (it sometimes *missed* them), and the "oracle" (ROBOT/HermiT) is
**itself order-sensitive** and misses them too on the OBO IRIs. The fix makes
hermit-rs build the forward, sub-chain-bearing role automaton directly and
order-independently. See the commit "build forward role automata directly so
inverse+chain sub-roles aren't dropped".

## How the divergence looked

`EFO_0000524 ≡ ∃EFO_0000784.UBERON_0000033` (head) `≡ ∃EFO_0000784.UBERON_0000974`
(neck). Role box: `RO_0004027 ⊑ EFO_0000784`, the chain
`RO_0004027 ∘ BFO_0000050 ⊑ RO_0004027`, `EFO_0000784` transitive with a declared
transitive inverse `EFO_0000785`. A disorder like
`MONDO_0004785 ≡ MONDO_0000001 ⊓ ∃RO_0004027.UBERON_0001711` (eyelid) is then a
head-disorder iff eyelid is part-of head — and it is:
`UBERON_0001711 →BFO_0000050→ UBERON_0000019 →BFO_0000050→ UBERON_0004088
→BFO_0000050→ UBERON_0000033`, with `BFO_0000050` transitive and the chain
lifting it onto `RO_0004027 ⊑ EFO_0000784`. So `MONDO_0004785 ⊑ EFO_0000524`
**holds**; likewise the other nine. hermit-rs derived them; ROBOT/HermiT did not.

## Why the oracle was wrong (and unreliable here)

ROBOT/HermiT's role-automaton construction has the *same* order-sensitivity this
whole effort is about. Renaming the ontology's IRIs to opaque names — leaving the
logical axioms byte-identical — flips ROBOT from "no" to "yes" on this
entailment. So ROBOT under-derives on the OBO IRIs purely because of its internal
HashMap iteration order. A reasoner whose answer depends on IRI spelling cannot
be a completeness oracle. (Soundness it still gives usefully: ROBOT never
asserted anything hermit-rs contradicts.)

Ground-truth checks that settle it:
* minimal `a⊑u, a∘b⊑a, b transitive, C≡∃u.Z, M⊑∃a.∃b.∃b.Z` — both hermit-rs and
  ROBOT derive `M⊑C`;
* the same with the efo OBO IRIs — hermit-rs yes, ROBOT no;
* rename those IRIs to short names — ROBOT flips to yes. Identical axioms.

## The actual bug (a completeness bug, order-dependent)

For a property `R` with a complex sub-property carrying a chain (`a ⊑ R`,
`a∘b ⊑ a`) **and** a declared inverse (`InverseObjectProperties(R, Ri)`):

* the dependency graph records only the forward sub-property edge `a ⊑ R`, never
  its mirror `Inv(a) ⊑ Inv(R)`;
* the recursion could be entered only on the inverse representations
  (`Inv(R)`/`Ri`), whose sub-property successors therefore omit `Inv(a)`;
* `R` itself was then produced by the mirror-fill pass as
  `mirror(automaton(Inv(R)))`, which lacks `R`'s sub-chains — so `R`'s automaton
  silently dropped `a∘b*`, `∀R.C` under-propagated, and the subsumption was
  missed. Which way it broke depended on iteration order (hence "sometimes").

Minimal reproducer (hermit-rs gave NO before the fix, YES after; ROBOT: YES):

```
a ⊑ u,  a∘b ⊑ a,  Transitive(b),  InverseObjectProperties(u, ui)
C ≡ ∃u.Z,  M ⊑ ∃a.Y1,  Y1 ⊑ ∃b.Y2,  Y2 ⊑ ∃b.Z      ⊢  M ⊑ C
```

## The fix

In `object_property_inclusion_manager.rs`, two minimal, order-independent changes:

1. **Seed the automaton recursion with every property** in the dependency graph,
   not only the sinks, so a forward property `R` is always built directly from
   its own sub-chains. Builds are memoised, so the extra seeds are no-ops.
2. **Guard the `R = mirror(complete(Inv(R)))` shortcut** so it only fires when `R`
   has no forward sub-properties of its own (otherwise the mirror would drop
   them).

## Validation

* The minimal reproducer and the efo entailments are now derived correctly and
  **deterministically** (EFO STAR modules classify identically across runs).
* All compiling suites pass: lib (312), `owl_wg_conformance`,
  `classification_tests`, `reasoner_tests`, `structural_tests`,
  `owlreasoner_api_tests`, `blocking_strategy_tests`. (`tableau_tests` has a
  pre-existing, unrelated `tuple_index` compile breakage.)
* The new EFO subsumptions were each confirmed to be genuine entailments by
  walking the part-of + subclass graph to head/neck.

## Tooling

`scripts/classification_diff.py` remains useful (transitive-closure
soundness/completeness diff with correct OWL functional-syntax parsing), but
**note its reference reasoner is order-sensitive**: treat ROBOT "rust-only" pairs
as *candidates* to verify (e.g. by re-running ROBOT on the IRI-renamed ontology),
not as confirmed unsoundness.
