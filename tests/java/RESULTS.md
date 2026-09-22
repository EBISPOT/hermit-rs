# Imported suite results

Measured against Java commit `37ec30aced32ac81ebecc5e33fad255ddefcb4c3`, after
the issue #8 inverse-role fix. All 598 declared Java methods are accounted for;
inherited methods also run under their individual-reuse and core-blocking suites.

| Executable cases | Pass | Fail | Empty upstream override |
| --- | ---: | ---: | ---: |
| Query/structural replay | 862 | 60 | 2 |
| Native internal tests | 50 | 3 | 0 |
| Total, excluding OWL WG | 912 | 63 | 2 |

These are strict-mode results, before applying expected-failure exceptions.
The Rust port does **not** yet have full Java test parity. The 63 failures are:

* **43 Rust/Java discrepancies**, including inherited repetitions: datatype
  consistency (URI, binary, datetime, numeric, plain/XML literals); property
  hierarchy and entailment results; direct results and hierarchy printing;
  three core-blocking Widmann scenarios; and description-graph/SWRL integration.
* **19 assertions that also fail in the pinned Java checkout**: 17 structural
  control comparisons and both blocking-validator tests. The original Java
  aggregate suites exclude these classes. The original controls and Java failure
  messages are retained, rather than rewritten to match Rust's output.
* **One resource limit**: individual-reuse classification of Dolce exceeds the
  512 MiB allocation budget. This is a failed case, not a consistency verdict.

Every case still executes in the default gate. `expected-failures.json` identifies
each discrepancy and its failing assertion. A new failure, a changed failing
assertion, or an unexpected pass fails CI; an unexpected pass requires removing
the stale exception. `HERMIT_JAVA_STRICT=1` disables exceptions. The default test
runner's accepted outcomes must not be read as the strict conformance pass count.

The separate OWL WG runner checks all 359 scoped cases: **212 pass, 147 skip**.
Of the skips, 143 have unconsumed logical RDF triples and four exceed the
15-second deadline (both checks for each of description-logic tests 208 and 209).
Every identity and outcome is checked against `tests/owl_wg/expected.tsv`.
Missing cases, wrong answers, newly skipped cases, changed skip reasons and
unexpectedly passing skips all fail the gate.

The import also exposed and fixed cached RDF class-expression reuse, finite
string enumeration traversing dead cycles, invalid language-tag membership,
finite URI intersections, and singleton dateTime value enumeration. The issue
#8 regressions separately cover the reproducer, reordered axioms, renamed roles,
valid chain entailments and explanations of inconsistent ontologies.

The commands and regeneration procedure are in [README.md](README.md). Tests
run serially in CI; isolated Java workers have a 120-second deadline and 512 MiB
allocation budget. These are Rust allocation limits, not a limit on all operating
system memory or on any external VM. Java trace generation uses `-Xmx256m`.
