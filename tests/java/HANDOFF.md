# Java parity handoff

The implementation work is paused at the user's request to conserve credits.
Continue on `rust`; the remaining work is recorded in the issues below.

## Completed and released

[`v2026-sep-22.1`](https://github.com/EBISPOT/hermit-rs/releases/tag/v2026-sep-22.1)
points to `880e7d1c036f5e6b4125b92ce2a9d008f4656f94`.
[Linux CI passed](https://github.com/EBISPOT/hermit-rs/actions/runs/35756467659),
as did the local serial release tests and focused tuple-identity regressions.

- Issue #8: preserve inverse role-chain automaton paths. Regressions cover the
  supplied minimal ontology, axiom order, property renaming, valid entailments,
  and explanations. The full RO input was not supplied for independent checking.
- Import all 598 declared Java test methods, including inherited configurations,
  with an inventory check and original source/fixture provenance.
- Isolate test workers, bound allocations, and kill/reap timed-out processes.
- Fix tuple predicate identity collisions that silently discarded constraints
  on Linux. Keep allocated identities distinct; do not use XOR-based hash keys
  as exact tuple equality.

## Required approach

The user explicitly said: **do not reproduce Java bugs**. Preserve the original
Java fixture/source, establish the corrected behavior independently, document the
evidence, and explicitly state any deliberate deviation from Java faithfulness
in the commit message. The empty-URI cardinality case below is a confirmed example.
Record a corrected replay expectation in [corrections.json](corrections.json),
beside the unchanged trace; see [README.md](README.md).

Run one local build/test/export job at a time. Use `CARGO_BUILD_JOBS=1`,
`OWLMAKE_CLASSIFY_THREADS=1`, and serial test execution. Retain the 512 MiB worker
allocation budget and existing deadlines; do not start a Lima/Docker VM. The user
previously exhausted RAM through a Lima virtual machine.

The default gate accepts only the exact recorded failures and rejects changed
failures or unexpected passes. **A green gate does not mean full Java parity.**
Use `HERMIT_JAVA_STRICT=1` for the actual assertions. Remove resolved exceptions
from `expected-failures.json` and update `RESULTS.md`; do not convert failures into
skips. Keep native test generators in sync with their generated ports.

[Regeneration and test commands](README.md), [measured results](RESULTS.md),
[complete inventory](inventory.json), and [failure baseline](expected-failures.json)
provide the starting point. Java is pinned to
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`.

## Suggested starting points

The property classifiers now reduce object roles to proxy concepts
`C_R = exists R.M` with a fresh inhabited marker `M`, and data roles to
`C_P = exists P.U` with a fresh unknown datatype `U`, and classify the proxies
with the concept classifier (#22). Their hierarchy looks up
`ObjectInverseOf(owl:topObjectProperty)` and
`ObjectInverseOf(owl:bottomObjectProperty)` as the built-in properties (#26).

The role automata no longer keep HermiT's `buildInversePropertiesMap` flaw
(**resolved**, deliberately deviating from Java). HermiT records
`SubObjectPropertyOf(R ObjectInverseOf(S))` as if `R` and `S` were inverses. With
`TransitiveObjectProperty(S)` it then derives `Inv(S) <= R` in class reasoning,
`isSubObjectPropertyExpressionOf` and the property classifiers. The automata are
now built from the role box as a grammar, per class of equivalent roles. A
brute-force comparison over random role boxes checks that each automaton accepts
exactly the entailed role words. See `ROLE_AUTOMATON_CONSTRUCTION.md` and
`tests/inverse_transitive_automaton_tests.rs`.

Two gaps that no imported case covers, found while fixing #26. The
`DisjointObjectProperties` entailment tests role atoms on the ontology's
tableau, where `owl:bottomObjectProperty` is axiomatized only when the ontology
mentions it; otherwise `DisjointObjectProperties(owl:bottomObjectProperty :r)`
is not entailed, as in Java, although the empty role is disjoint from every
role. And `isFunctional`/`isInverseFunctional` test `owl:Thing <= max 1 P`,
which rejects a non-simple `P` (a transitive property or
`owl:topObjectProperty`) that Java's role atoms answer.

Inequalities between two constant data nodes are compared by value
(**resolved**, no issue). They were never checked, because the inequality
components start only from non-constant nodes, so
`DataPropertyAssertion(:dp :a "1"^^xsd:int)` with
`NegativeDataPropertyAssertion(:dp :a "01"^^xsd:int)` was consistent. See
`tests/constant_data_inequality.rs`.

`xsd:dateTime` `24:00:00` is the same value as `00:00:00` of the next day
(**resolved**, no issue, deliberately deviating from Java). HermiT's last-day
flag kept the two spellings apart, so a functional data property asserted with
both was inconsistent and each local midnight was counted twice. Six
`DateTimeTest` expectations are corrected in [corrections.json](corrections.json);
see `tests/datetime_24h.rs` and [RESULTS.md](RESULTS.md).

An `xsd:base64Binary` literal denotes a base64Binary value (**resolved**, no
issue, deliberately deviating from Java). HermiT's `BinaryData.parseBase64Binary`
tagged it as hexBinary, so `"QQ=="^^xsd:base64Binary` was outside
xsd:base64Binary and equal to `"41"^^xsd:hexBinary`, although OWL 2 makes the
two value spaces disjoint. The `BinaryDataTest.testBase64Parsing` expectation is
corrected in [corrections.json](corrections.json); see
`tests/base64_binary_value_space.rs`.

A NaN bound on xsd:float or xsd:double empties the range (**resolved**, no
issue, deliberately deviating from Java, which drops a NaN double bound and a
NaN float max* bound), and lexical forms outside the XSD 1.1 grammars are
ill-typed (**resolved**, no issue): base64Binary with nonzero padding bits,
boolean case variants, decimal exponents, float/double type suffixes and
over-padded dateTime years; `"+INF"` is accepted. See
`tests/nan_bounds_and_lexical_validation.rs` and [RESULTS.md](RESULTS.md),
which lists the lexical leniencies deliberately kept.

String lengths count characters, patterns have their XSD meaning, and length
windows are reasoned about symbolically (**resolved**, no issue; the first two
deliberately deviate from Java). HermiT counts UTF-16 code units, so U+10000
had length 2; `\d`, `\w` and `.` followed dk.brics or the `regex` crate; and
`xsd:string[pattern "a*", minLength 2147483000]` built one automaton state per
length and exhausted memory. See `tests/string_datatype_edge_cases.rs` and
[RESULTS.md](RESULTS.md).

Large value spaces, anonymous constants, unsupported dateTime values and the
`Infinity` spellings (**resolved**, no issue; rejecting `"Infinity"` deviates
from Java and corrects `DatatypesTest.testINF`). Cliques of more than 4096
nodes compared unlisted value spaces by count, survivors were listed only up to
4096 values, a string count over more than 160 states saturated, and a
`DataOneOf` holding an anonymous constant was infinite. See
`tests/datatype_robustness.rs` and [RESULTS.md](RESULTS.md).

Exact dateTime values, large bounded repetitions and the exponential
assignment search (**resolved**, no issue; accepting years beyond ±9999 and
fractions finer than milliseconds deviates from Java, which rejects them).
Instants are exact, a top-level `R{m,n}` among fixed-length pieces is a length
window, and an all-different component is decided by bipartite matching. Still
open: a large repetition nested in a group or beside a piece of varying length
builds one state per copy, a string count over a large, dense automaton
saturates at the work budget, and an anyURI space too large to list is counted
by an upper bound.

Several datatype failures share missing subtraction of negative ranges or
excluded values during cardinality counting/enumeration. Keep emptiness,
cardinality, and inequality assignment consistent.

Nineteen failing assertions also failed in the pinned Java checkout. These require
investigation of obsolete controls or fixtures, not blindly changing Rust to
match them. The two `BlockingValidatorTest` fixtures are repaired (#32, #33;
see `corrected/` and [RESULTS.md](RESULTS.md)). Issues #35 to #50 are
resolved by a semantic clause comparison (see [RESULTS.md](RESULTS.md)). The
last structural control, `NormalizationTest.testKeys2` (#51), drops a data
property from the key. Its corrected expectation is in
[corrections.json](corrections.json). The same fix makes keys on complex classes
apply, which is a deliberate deviation from Java. Original Java error traces are
retained in the case fixtures and `upstream-failures.json`.

## Imported Java failures

43 issues cover all 63 failing executable cases. Duplicate inherited failures
are grouped; every issue lists its exact cases, reproduction command, findings,
and acceptance criteria. At the release baseline, 912 imported cases pass and
two overrides are empty in the original Java source. All 43 are now resolved.
In strict mode, all 975 executable cases pass and `expected-failures.json` is
empty. Ten of those passes use documented corrections of the Java expectation
(#9, #51, six dateTime `24:00:00` cases, one base64Binary case and
`DatatypesTest.testINF`).

| Issue | Work | Cases |
| --- | --- | ---: |
| [#9](https://github.com/EBISPOT/hermit-rs/issues/9) | Correct the Java empty-URI cardinality expectation (**resolved**; see [corrections.json](corrections.json)) | 1 |
| [#10](https://github.com/EBISPOT/hermit-rs/issues/10) | Respect excluded URI values in finite pattern/length intersections (**resolved**) | 1 |
| [#11](https://github.com/EBISPOT/hermit-rs/issues/11) | Respect URI exclusions after complementing a length restriction (**resolved** with #10) | 1 |
| [#12](https://github.com/EBISPOT/hermit-rs/issues/12) | Count finite binary ranges after subtracting length restrictions (**resolved**) | 1 |
| [#13](https://github.com/EBISPOT/hermit-rs/issues/13) | Keep individual-reuse classification of Dolce within the worker memory budget (**resolved** with #22) | 1 |
| [#14](https://github.com/EBISPOT/hermit-rs/issues/14) | Count dateTime boundary values after subtracting an open interval (**resolved**) | 1 |
| [#15](https://github.com/EBISPOT/hermit-rs/issues/15) | Enumerate finite mixed numeric ranges for inequality assignment (**resolved**) | 1 |
| [#16](https://github.com/EBISPOT/hermit-rs/issues/16) | Subtract enumerated exclusions from mixed numeric value spaces (**resolved** with #15) | 1 |
| [#17](https://github.com/EBISPOT/hermit-rs/issues/17) | Detect an empty plain-literal range after excluding its sole value (**resolved**) | 1 |
| [#18](https://github.com/EBISPOT/hermit-rs/issues/18) | Infer data-property subsumption forced by singleton values (**resolved** with #22) | 3 |
| [#19](https://github.com/EBISPOT/hermit-rs/issues/19) | Return only the most specific direct individual types (**resolved**) | 3 |
| [#20](https://github.com/EBISPOT/hermit-rs/issues/20) | Correct property hierarchy axioms emitted by printHierarchies (**resolved** with #22) | 3 |
| [#21](https://github.com/EBISPOT/hermit-rs/issues/21) | Avoid declaring built-in bottom classes in collapsed hierarchies (**resolved**) | 3 |
| [#22](https://github.com/EBISPOT/hermit-rs/issues/22) | Infer role subsumption implied by chains and existential restrictions (**resolved**) | 3 |
| [#23](https://github.com/EBISPOT/hermit-rs/issues/23) | Infer role subsumption forced by nominals and transitivity (**resolved** with #22) | 3 |
| [#24](https://github.com/EBISPOT/hermit-rs/issues/24) | Classify role subsumption with chains, transitivity and symmetry (**resolved** with #22) | 3 |
| [#25](https://github.com/EBISPOT/hermit-rs/issues/25) | Recognize equivalent data properties forced to a common singleton range (**resolved** with #22) | 3 |
| [#26](https://github.com/EBISPOT/hermit-rs/issues/26) | Normalize inverse built-in roles in property hierarchy queries (**resolved**) | 3 |
| [#27](https://github.com/EBISPOT/hermit-rs/issues/27) | Recognize object properties equivalent to the universal role (**resolved** with #22) | 3 |
| [#28](https://github.com/EBISPOT/hermit-rs/issues/28) | Reject the first unsatisfiable Widmann case under core blocking (**resolved**) | 1 |
| [#29](https://github.com/EBISPOT/hermit-rs/issues/29) | Reject the second unsatisfiable Widmann case under core blocking (**resolved** with #28) | 1 |
| [#30](https://github.com/EBISPOT/hermit-rs/issues/30) | Reject the third unsatisfiable Widmann case under core blocking (**resolved** with #28) | 1 |
| [#31](https://github.com/EBISPOT/hermit-rs/issues/31) | Reject intersections of XMLLiteral and disjoint datatype spaces (**resolved**) | 1 |
| [#32](https://github.com/EBISPOT/hermit-rs/issues/32) | Repair the obsolete annotated-equality blocking-validator fixture (**resolved**; see `corrected/`) | 1 |
| [#33](https://github.com/EBISPOT/hermit-rs/issues/33) | Repair the obsolete one-invalid-block validator fixture and check its assertions (**resolved** with #32) | 1 |
| [#34](https://github.com/EBISPOT/hermit-rs/issues/34) | Apply description-graph rules to anonymous graph vertices (**resolved**) | 1 |
| [#35](https://github.com/EBISPOT/hermit-rs/issues/35) | Compare datatype clausification semantically: testDataComplementOf3 (**resolved**) | 1 |
| [#36](https://github.com/EBISPOT/hermit-rs/issues/36) | Compare datatype clausification semantically: testDataComplementOf4 (**resolved** with #35) | 1 |
| [#37](https://github.com/EBISPOT/hermit-rs/issues/37) | Compare datatype clausification semantically: testDataPropertiesDataComplementOf1 (**resolved** with #35) | 1 |
| [#38](https://github.com/EBISPOT/hermit-rs/issues/38) | Compare datatype clausification semantically: testDataPropertiesDataComplementOf2 (**resolved** with #35) | 1 |
| [#39](https://github.com/EBISPOT/hermit-rs/issues/39) | Compare datatype clausification semantically: testDataPropertiesDataOneOf1 (**resolved** with #35) | 1 |
| [#40](https://github.com/EBISPOT/hermit-rs/issues/40) | Compare datatype clausification semantically: testDataPropertiesDataOneOf2 (**resolved** with #35) | 1 |
| [#41](https://github.com/EBISPOT/hermit-rs/issues/41) | Compare datatype clausification semantically: testDataPropertiesDataOneOf3 (**resolved** with #35) | 1 |
| [#42](https://github.com/EBISPOT/hermit-rs/issues/42) | Compare datatype clausification semantically: testDataPropertiesDataOneOf4 (**resolved** with #35) | 1 |
| [#43](https://github.com/EBISPOT/hermit-rs/issues/43) | Compare datatype clausification semantically: testDataPropertiesHasValue1 (**resolved** with #35) | 1 |
| [#44](https://github.com/EBISPOT/hermit-rs/issues/44) | Compare datatype clausification semantically: testDataPropertiesHasValue2 (**resolved** with #35) | 1 |
| [#45](https://github.com/EBISPOT/hermit-rs/issues/45) | Modernize the transitive-role clausification control without weakening semantics (**resolved**; compared by automaton language) | 1 |
| [#46](https://github.com/EBISPOT/hermit-rs/issues/46) | Compare clausification auxiliaries modulo consistent renaming (**resolved** with #35) | 1 |
| [#47](https://github.com/EBISPOT/hermit-rs/issues/47) | Restore the nominal clausification control: testNominals1 (**resolved** with #45) | 1 |
| [#48](https://github.com/EBISPOT/hermit-rs/issues/48) | Restore the nominal clausification control: testNominals2 (**resolved** with #45) | 1 |
| [#49](https://github.com/EBISPOT/hermit-rs/issues/49) | Restore the nominal clausification control: testNominals3 (**resolved** with #45) | 1 |
| [#50](https://github.com/EBISPOT/hermit-rs/issues/50) | Restore the nominal clausification control: testNominals4 (**resolved** with #45) | 1 |
| [#51](https://github.com/EBISPOT/hermit-rs/issues/51) | Correct the upstream key-normalization expectation that drops a data property (**resolved**; see [corrections.json](corrections.json)) | 1 |

## OWL WG conformance

The separate suite passes all 359 scoped cases, with no skips.
These three issues cover the RDF parsing skips and both checks for each of
the two formerly timed-out reasoning cases. They are separate from the 63 Java failures.

- [#52: Expand RDF parser coverage for 143 skipped OWL WG cases](https://github.com/EBISPOT/hermit-rs/issues/52)
  (**resolved**: all 143 pass; the last five are explained in
  [RESULTS.md](RESULTS.md))
- [#53: Resolve the OWL WG description-logic 208 reasoning timeout](https://github.com/EBISPOT/hermit-rs/issues/53)
  (**resolved**: lazy unfolding of acyclic definitorial TBoxes in consistency checks)
- [#54: Resolve the OWL WG description-logic 209 reasoning timeout](https://github.com/EBISPOT/hermit-rs/issues/54)
  (**resolved** with #53)
