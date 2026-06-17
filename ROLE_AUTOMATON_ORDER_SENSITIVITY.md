# Role-automaton construction is order-sensitive (a divergence rooted in Java HermiT)

This documents a non-determinism / soundness issue found while classifying **EFO**
with the Rust port, the fix that has been applied, and — importantly — direct
evidence that the underlying fragility is in **Java HermiT itself**, not just the
port. It is written to be manually reviewed before deciding how far to take the
fix.

## Symptom

Classifying EFO with the Rust port produced **non-deterministic output**: repeated
runs of `hermit -c` on the same ontology gave different class hierarchies
(intermittently introducing spurious subsumptions such as several `MONDO_*`
classes becoming subclasses of `EFO_0000524` "head and neck disorder", which
`robot`/HermiT does **not** infer).

## Root cause

The non-determinism originates in `structural::object_property_inclusion_manager`
(`ObjectPropertyInclusionManager`), which builds, for every complex object
property `R`, a finite automaton whose language is the set of role chains implied
to be sub-roles of `R` (the standard regular-RIA encoding). The construction:

* keeps its working automata in `HashMap`/`HashSet`-keyed collections, and
* **enriches automata in place** as it iterates them — in particular
  `increase_automaton_with_inverse` splices (the mirror of) a property's inverse
  automaton via `automata_connector`, which performs a **disjoint union of states**.

Because the splice adds states, the automaton a property ends up with **depends on
the order** in which these collections are iterated, and whether the inverse it is
enriched with has *already* been enriched. Under a "bad" order, `R` is enriched
with an inverse that already contains `mirror(R)`, so `R` re-absorbs its own
language (visible as extra `all:N(X) :- all:N(X)` state self-inclusions) and
`∀R.C` over-propagates → spurious subsumptions.

Java's `HashMap`/`HashSet` iteration is stable across runs (its hashing is
content-based and unseeded), so Java is reproducible. Rust's
`std::collections::HashMap` uses `RandomState` (re-seeded per process), so the
port iterated differently every run → different automaton → non-deterministic
output (sometimes under-enriched ⇒ incomplete, sometimes over-enriched ⇒ unsound).

## This is order-sensitivity *in Java HermiT*, not just the port

The key finding: **HermiT's construction is itself order-sensitive — its
correctness depends on its particular HashMap iteration order.** Verified by
forcing Java HermiT to iterate the same collections in a *different* (sorted)
order and observing its output change from sound to unsound.

Instrumentation (on the `java` branch, `ObjectPropertyInclusionManager`): sort the
two order-sensitive iterations by `toString`:

```java
// recursion start:
for (OWLObjectPropertyExpression superproperty : __sorted(propertiesToStartRecursion)) ...
// sub-property substitution in buildCompleteAutomataForProperties:
for (OWLObjectPropertyExpression smallerProperty : __sorted(inversedPropertyDependencyGraph.getSuccessors(propertyToBuildAutomatonFor))) ...
// where:
private static java.util.List<OWLObjectPropertyExpression> __sorted(java.util.Collection<OWLObjectPropertyExpression> c){
    java.util.List<OWLObjectPropertyExpression> l=new java.util.ArrayList<>(c);
    l.sort(java.util.Comparator.comparing(Object::toString));
    return l;
}
```

Then run Java HermiT's own `--dump-clauses` / `-c` on an EFO STAR module:

| Java HermiT | `efo_min` clauses / spurious | `efo_big` clauses / spurious |
|---|---|---|
| **default** (hash order) | 550 / **0** ✓ | 17519 / **0** ✓ |
| **sorted** iteration (same code) | 550 / 0 | **18661 / 5** ✗ |

So Java HermiT itself, under a merely *different deterministic* iteration order,
emits **5 spurious subsumptions** on `efo_big`. The Rust port under a sorted order
produces the same wrong result (18861 / 5; the ~200-clause delta from Java is only
horned-owl vs OWLAPI parse order), which also demonstrates the **port is faithful**
— it reproduces Java's exact order-sensitivity.

## Fix applied (faithful, deterministic)

Commit: *"iterate role-automaton construction in a canonical order"*. Every
order-sensitive collection in the construction is now iterated in a fixed
`prop_sort_key` order. This makes the Rust output **fully deterministic** and, on
`efo_min`, **byte-identical to Java HermiT** (`--dump-clauses` matches modulo
internal-concept renaming; 0 spurious). The crate's 312 lib unit tests pass.

## Residual divergence (needs a decision)

On `efo_big` the deterministic Rust output (and equally, sorted-order *Java*)
over-enriches → 5 spurious subsumptions, because the chosen canonical order is not
Java's *default* hash order, and the construction is genuinely non-confluent on
complex inverse/chain hierarchies. Options:

1. **Reproduce Java's exact `HashMap` iteration order** — not robustly feasible
   (depends on OWLAPI's `OWLObjectPropertyExpression.hashCode()` and `HashMap`
   bucketing/resize history; would not generalize across OWLAPI versions).
2. **Confluent re-derivation** of the construction so it computes the correct RIA
   closure regardless of order. Two attempts were made and both failed, which
   *localises* the problem precisely:
   * **(a) forward-closure** — enrich `R` with the inverse's *forward* sub-chain
     closure rather than its live mutually-enriched automaton: removes some
     over-enrichment but **under-enriches** (`efo_min` 445 < 550).
   * **(b) semi/complete fixpoint** — enrich with the inverse's *semi* automaton
     (sub-chains splicing each sub-property's *complete* automaton, no inverse
     enrichment), per `complete(R) = semi(R) ∪ mirror(semi(Inv(R)))`: still
     **under-enriches** (`efo_min` 441, `efo_big` 17035) **and the `efo_big` 5
     spurious persist**.
   * The fact that the 5 spurious survive *both* re-routings of the
     inverse-enrichment passes — combined with sorted-order *Java* reproducing
     them by reordering **only** `propertiesToStartRecursion` + the sub-property
     iteration — proves the over-enrichment originates in the **recursion's
     mutual-inverse build order** (which member of a `{R, Inv(R)}` pair is built
     and cached first), *not* in the standalone inverse-enrichment passes. A
     correct confluent fix must therefore build a **canonical representative** of
     each `{R, Inv(R)}` pair and derive the other strictly as its mirror, so the
     representative's automaton does not depend on build order. This is the
     recommended direction; it needs careful design and clause-for-clause
     validation against Java's `--dump-clauses`.
3. **Report upstream**: the order-fragility is arguably a latent bug in HermiT's
   automaton construction; its soundness on a given ontology depends on JVM/OWLAPI
   `HashMap` iteration order.

## Reproduction

```bash
# robot (bundles Java HermiT) and an EFO STAR module are used as the oracle.
robot extract --method STAR -i efo.owl -T seeds.txt -o efo_min.owl
robot convert -i efo_min.owl -f ofn -o efo_min.ofn

# Rust port (after the determinism fix): deterministic, efo_min matches Java.
hermit -c efo_min.ofn | grep -c 'EFO_0000524> )$'      # => 0

# Java HermiT clause dump (jautomata is a system-scope dep; add it to the cp):
java -cp hermit-cli.jar:jautomata-core-2.0-alpha-1.jar \
     org.semanticweb.HermiT.cli.CommandLine --dump-clauses=- efo_min.ofn
```
