# Role-automaton over-acceptance on `efo_big` — investigation

Follow-up to `ROLE_AUTOMATON_ORDER_SENSITIVITY.md`. That note fixed the
*non-determinism* (the construction is now deterministic) and documented that a
residual divergence from Java HermiT remains on `efo_big`. This note pins that
divergence down with an oracle and rules out several fix hypotheses, so the
eventual fix has a precise target and a validation tool.

## Validation tooling (new)

`scripts/classification_diff.py` diffs a hermit-rs `-c` classification against a
reference reasoner (ROBOT running Java HermiT) over the **transitive closures**
of both hierarchies, restricted to the shared class vocabulary. It correctly
parses OWL functional syntax (stripping `Annotation(...)` wrappers, expanding
`Prefix(...)`), which an earlier naive diff did not — that naive diff produced
thousands of false "spurious" pairs (e.g. `MONDO_0000462 ⊑ MONDO_0000001`, a
disease under the disease root) purely because annotated/prefixed oracle axioms
were skipped. With correct parsing the picture is clean.

Note: Java HermiT's own CLI jar does not run in this environment (a
cglib/Guice `ExceptionInInitializerError` on the available JVM); ROBOT's bundled
HermiT does run and is used as the oracle.

## Exact divergence

| Module | rust clauses | SPURIOUS (unsound) | MISSING (incomplete) |
|--------|-------------:|-------------------:|---------------------:|
| `efo_min` | 550 (= Java) | **0** | **0** |
| `efo_big` | 18861 (Java ≈ 17519) | **10** | **0** |

So hermit-rs is **complete** on both modules and **sound on `efo_min`**; the
only errors on `efo_big` are 10 spurious subsumptions, all of the form
`MONDO_xxxxxxx ⊑ EFO_0000524` ("head and neck disorder"):

```
MONDO_0002708 0004785 0004804 0005800 0005885 0006918 0006950 0016047 0020283 0023865  ⊑  EFO_0000524
```

## Confirmed genuinely spurious (worked example)

`EFO_0000524 ≡ ∃EFO_0000784.UBERON_0000033` (head). Take `MONDO_0004785`:

* `MONDO_0004785 ≡ MONDO_0000001 ⊓ ∃RO_0004027.UBERON_0001711` (eyelid).
* Role box: `RO_0004027 ⊑ EFO_0000784`, and the chain
  `RO_0004027 ∘ BFO_0000050 ⊑ RO_0004027`; `EFO_0000784` is transitive with
  inverse `EFO_0000785` (also transitive).
* Hence `MONDO_0004785 ⊑ EFO_0000524` holds **iff**
  `UBERON_0001711 ⊑ ∃BFO_0000050.UBERON_0000033` (eyelid part-of head).
* But in `efo_big`, eyelid's only part-of axiom is
  `UBERON_0001711 ⊑ ∃BFO_0000050.UBERON_0000019` — **not** head. So the
  subsumption does **not** hold; the oracle correctly omits it and hermit-rs
  wrongly derives it.

The trigger structure is exactly the order-sensitive configuration from the
first note: a transitive property `EFO_0000784` with a transitive inverse, a
sub-property `RO_0004027` carrying its own `∘ BFO_0000050` chain. The spurious
subsumptions arise because `EFO_0000784`'s role automaton **over-accepts** a
chain, so the `∀EFO_0000784`-rewriting of `¬EFO_0000524` clashes where it
should not.

## Hypotheses ruled out this round

* **Inverse-enrichment is NOT the locus.** Re-deriving the construction as the
  confluent fixpoint `complete(R) = semi(R) ∪ mirror(semi(Inv(R)))` (enriching
  from each property's *semi* = inverse-free sub-chain closure instead of its
  complete automaton) changed the total clause count (18861 → 17035) but left
  the classification **byte-identical** — still exactly the same 10 spurious,
  still 0 missing — while *regressing* `efo_min` faithfulness (550 → 441
  clauses). It was reverted. The over-accepted chain therefore lives in the
  **forward / transitive / chain-composition** part of `EFO_0000784`'s
  automaton, not in the inverse passes.
* **A minimal synthetic reproducer does not trigger it.** A hand-built ontology
  with the same role box (`u` transitive, `Inv(u)=v` transitive, `a ⊑ u`,
  `a∘b ⊑ a`, `C ≡ ∃u.Z`, `X ≡ Root ⊓ ∃a.Y`, `Y ⊑ ∃b.W`) does **not** produce
  the spurious `X ⊑ C` — hermit-rs answers correctly. The bug needs the full
  `efo_big` scale (the second `EFO_0000524 ≡ ∃EFO_0000784.UBERON_0000974`
  equivalence, the sibling `RO_0004024/5/6 ∘ BFO_0000050` chains, and the MONDO
  hierarchy) to manifest, so minimal-case debugging is not yet available.

## Where the fix likely is, and how to validate it

The remaining work is to make `EFO_0000784`'s **forward** automaton accept
exactly its RIA closure under transitivity + the `RO_0004027 ∘ BFO_0000050`
chain — no more. The construction is HermiT's most intricate component and is
order-sensitive (Java's default hash order happens to avoid the over-acceptance;
a sorted order — in Java too, per the first note — reproduces it), so the fix
must be a genuinely confluent forward/transitive/chain construction validated
clause-for-clause, not another iteration-order tweak.

`scripts/classification_diff.py` against the ROBOT/HermiT oracle on `efo_big`
(target: SPURIOUS 0, MISSING 0) plus the `efo_min` clause count (target: 550)
is the validation harness; the `efo_big` loop runs in seconds.
