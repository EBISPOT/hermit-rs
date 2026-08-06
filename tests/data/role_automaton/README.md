# Role-automaton reproducers

Minimal OWL functional-syntax ontologies for the inverse + chain role-automaton
completeness behaviour described in `ROLE_AUTOMATON_CONSTRUCTION.md`. Each is a
self-contained EFO STAR-module fragment small enough to read and to run by hand:

```
hermit -c tests/data/role_automaton/<file>.ofn
```

The minimal case is also encoded as a programmatic regression test in
`tests/inverse_chain_transitivity_tests.rs`
(`forward_sub_chain_survives_declared_inverse`).

## `inverse_chain_completeness.ofn`

The minimal case the completeness fix guarantees. Property `u` has a chain-bearing
sub-property (`a ⊑ u`, `a ∘ b ⊑ a`, `b` transitive) **and** a declared inverse
(`InverseObjectProperties(u, ui)`). With `C ≡ ∃u.Z` and
`M ⊑ ∃a.∃b.∃b.Z`, the role chain lifts the part-of (`b`) steps onto `a ⊑ u`, so:

```
M ⊑ C        (entailed)
```

Java derives this one, and so do we. (`u`'s automaton must not be taken as the
mirror of its inverse here, which would lose `u`'s `a ∘ b*` sub-chain.)

## `efo_pattern.ofn`

The same pattern with the real EFO/OBO IRIs it was found on:
`EFO_0000524 ≡ ∃EFO_0000784.UBERON_0000033` (head), `RO_0004027 ⊑ EFO_0000784`,
`RO_0004027 ∘ BFO_0000050 ⊑ RO_0004027`, `BFO_0000050` (part-of) transitive, and
`MONDO_0004785 ⊑ ∃RO_0004027.UBERON_0001711` (eyelid) with eyelid part-of head via
`UBERON_0000019 → UBERON_0004088 → UBERON_0000033`. HermiT does **not** derive `MONDO_0004785 ⊑ EFO_0000524` here — see
`efo_pattern_renamed.ofn` below.

## `efo_pattern_renamed.ofn`

`efo_pattern.ofn` with the IRIs renamed to opaque short names and the logical
axioms left identical. HermiT derives `M ⊑ C` on this file but *not* on
`efo_pattern.ofn`, even though the two are logically identical: the automaton a
property ends up with depends on the order `connectAllAutomata` walks
`propertiesToStartRecursion`, a `java.util.HashSet`, and that order is a function
of the IRI spelling.

That is not a licence to answer differently. We reproduce HermiT's answer on each
of the three files, IRI sensitivity included — see
`tests/role_automaton_java_parity_tests.rs`. Deriving the entailment on
`efo_pattern.ofn` anyway (by seeding the recursion with every property rather than
Java's sinks only) put eight subclass edges into EFO's released `efo.owl` that
ROBOT does not emit.
