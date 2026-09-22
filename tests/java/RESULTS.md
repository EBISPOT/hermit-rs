# Imported suite results

Measured against Java commit `37ec30aced32ac81ebecc5e33fad255ddefcb4c3`, after
the issue #8 inverse-role fix, the issue #9 expectation correction, the issue
#10/#11 excluded-URI fix, the issue #12 binary-length fix, the issue #14
dateTime-interval fix and the issue #15/#16 numeric value-space fix. All 598
declared Java methods are accounted for; inherited methods also run under their
individual-reuse and core-blocking suites.

| Executable cases | Pass | Fail | Empty upstream override |
| --- | ---: | ---: | ---: |
| Query/structural replay | 869 | 53 | 2 |
| Native internal tests | 50 | 3 | 0 |
| Total, excluding OWL WG | 919 | 56 | 2 |

These are strict-mode results, before applying expected-failure exceptions.
The Rust port does **not** yet have full Java test parity. The 56 failures are:

* **36 Rust/Java discrepancies**, including inherited repetitions: datatype
  consistency (plain/XML literals); property hierarchy and entailment results;
  direct results and hierarchy printing; three core-blocking Widmann scenarios;
  and description-graph/SWRL integration.
* **19 assertions that also fail in the pinned Java checkout**: 17 structural
  control comparisons and both blocking-validator tests. The original Java
  aggregate suites exclude these classes. The original controls and Java failure
  messages are retained, rather than rewritten to match Rust's output.
* **One resource limit**: individual-reuse classification of Dolce exceeds the
  512 MiB allocation budget. This is a failed case, not a consistency verdict.

One pass deliberately deviates from Java. `reasoner.AnyURITest.testIntersection`
expects `xsd:anyURI[minLength 0]` intersected with the complement of
`xsd:anyURI[minLength 1]` to be empty, but under XSD 1.1 and the OWL 2 Direct
Semantics it contains exactly the empty URI (issue #9). Java misses it because
dk.brics `getFiniteStrings` omits the empty word of a non-singleton automaton.
The trace keeps Java's `false`; [corrections.json](corrections.json) records the
corrected `true`, its evidence and independent membership and cardinality
regressions.

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

Issues #10 and #11 had one cause. An excluded value (a negated `DataOneOf`)
stopped an `xsd:anyURI` value space from being built as a string automaton, so a
pattern bounded only by a length window or a complemented length restriction
counted as infinite, and its excluded values were never subtracted. Excluded
anyURI values are now removed from the automaton; literals of other datatypes
remove nothing. The string automaton lacks supplementary-plane characters (and
U+FFFE/U+FFFF), which anyURI values may contain, so it is no longer used when the
patterns admit one; the enumerating fallback counts those values instead. The
regressions cover the remaining values, cardinality and distinct-value
assignment.

Issue #12 was a similar gap in binary data. The binary value space took its
length window from the positive restrictions only. So
`xsd:hexBinary[minLength 0]` outside `xsd:hexBinary[minLength 1]` counted as
infinite, and two distinct values fitted, although only the empty octet
sequence remains. The binary value space now follows HermiT's
`BinaryDataValueSpaceSubset`: it subtracts each negated length window of the
same datatype, then the excluded values in the remaining windows. The emptiness
check, the cardinality and the distinct-value assignment all use it. A negated
restriction of the other binary datatype removes nothing, because the two value
spaces are disjoint.

Issue #14 was the same gap for dateTime. The dateTime value space took its
intervals from the positive restrictions only. So the closed interval between
`1965-04-15T00:00:00` and `1965-05-01T00:00:00`, outside its open interior,
counted as infinite, and five distinct values fitted, although only the two
bounds remain. The dateTime value space now follows HermiT's
`DateTimeValueSpaceSubset`. It treats values with a timezone offset and values
without one separately: it subtracts the interval that each negated dateTime
restriction gives that kind, then the excluded values that remain. A bound of
the other kind is widened by the 14-hour offset window and made exclusive,
because a value within 14 hours of it is incomparable with it (XSD 1.1 Part 2
§D.2.1). An interval that spans two instants is infinite; a single instant is
counted exactly. The emptiness check, the cardinality and the distinct-value
assignment all use it. Enumerating these values also removed a false clash: two
different single-instant ranges with the same count were treated as one value
space, so two values that had to differ clashed.

The count at a single instant follows HermiT, which counts `24:00:00` as a
value separate from `00:00:00` of the next day, and so treats the two spellings
as different constants. XSD 1.1 maps both spellings to one value (Part 2
§3.3.7.2, §E.3.5 and §E.3.1). So asserting both spellings for a functional
data property clashes, wrongly, in Java as in Rust. `DateTimeTest.testFinite1_1`
and `testFinite2_1` pass only because of the extra value: under XSD 1.1 their
ranges hold one and two values, fewer than the two and four they require.
Three native `DateTimeInterval` tests assert the same representation.
Correcting it is left to a separate change.

Issues #15 and #16 had one cause, in the numeric value spaces. owl:real,
owl:rational, xsd:decimal and the integer datatypes share one value space, whose
values nest (OWL 2 Structural Specification §4.1). It was counted from the
positive restrictions, and a negated restriction or an excluded value was
subtracted on some paths only. The ranges of `NumericsTest.testDecimalMinusInt*`
hold the xsd:int values from 1.2 to 7.2 that are not integers from 2.2 to 5.2,
which are 2, 6 and 7. The count was right, but the values were never listed, and
the distinct-value assignment gives up on a space it cannot list, so a value
distinct from 2, 6.0 and 7.0 was taken to exist (#15). Excluding those three
values subtracted nothing, and the space counted as infinite (#16). The value
space now follows HermiT's `OWLRealValueSpaceSubset`: it intersects the
intervals of the positive restrictions, subtracts each negated restriction of
these datatypes, then the excluded values that remain. The emptiness check, the
cardinality and the distinct-value assignment all use it. xsd:float and
xsd:double, whose value spaces are disjoint from it and from each other (§4.2),
are built the same way. Listing small spaces also removed a false clash: two
nodes that had to differ, each confined to a different single number of a dense
range, clashed, because unlisted spaces with the same count were treated as one
value space.

Two corrections deviate from Java; no Java case depends on either, and both make
the value space agree with the membership test. A float or double range with
ordering facets never holds NaN (XSD 1.1 Part 2 §3.3.4.1 and §3.3.5.1), so its
complement does. HermiT drops NaN when it subtracts such a range from the whole
value space, and so did Rust: `xsd:float` outside `xsd:float[minInclusive -INF]`
counted as empty, but it is `{NaN}`. And HermiT's
`Numbers.getNearestIntegerInBound` subtracts 11 instead of 1 from an exclusive
upper bound of -2147483648, which dropped the ten integers from -2147483658 to
-2147483649. A NaN facet bound still follows HermiT: xsd:double ignores it, and
xsd:float ignores it in `maxInclusive` and `maxExclusive`, although under XSD
1.1 such a range is empty. Correcting that is left to a separate change.

The commands and regeneration procedure are in [README.md](README.md). Tests
run serially in CI; isolated Java workers have a 120-second deadline and 512 MiB
allocation budget. These are Rust allocation limits, not a limit on all operating
system memory or on any external VM. Java trace generation uses `-Xmx256m`.
