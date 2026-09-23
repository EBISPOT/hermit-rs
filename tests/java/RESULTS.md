# Imported suite results

Measured against Java commit `37ec30aced32ac81ebecc5e33fad255ddefcb4c3`, after
the issue #8 inverse-role fix, the issue #9 expectation correction, the issue
#10/#11 excluded-URI fix, the issue #12 binary-length fix, the issue #14
dateTime-interval fix, the issue #15/#16 numeric value-space fix, the issue #17
string value-space fix, the issue #31 XMLLiteral disjointness fix, the issue
#22 property classification fix, which also resolved #13, #18, #20, #23, #24,
#25 and #27, the issue #26 fix for the inverses of the built-in object
properties, the issue #19 fix for the direct types of individuals, the issue
#21 fix for the declarations in printed hierarchies, the issue #28
core-blocking fix, which also resolved #29 and #30, the issue #32/#33
blocking-validator fixture repair, the issue #34 description-graph rule
fix, and the semantic clause comparison for issues #35 to #50. All 598
declared Java methods are accounted for; inherited methods also run under their
individual-reuse and core-blocking suites.

| Executable cases | Pass | Fail | Empty upstream override |
| --- | ---: | ---: | ---: |
| Query/structural replay | 921 | 1 | 2 |
| Native internal tests | 53 | 0 | 0 |
| Total, excluding OWL WG | 974 | 1 | 2 |

These are strict-mode results, before applying expected-failure exceptions.
The Rust port does **not** yet have full Java test parity. The remaining failure
is an assertion that also fails in the pinned Java checkout: the
`NormalizationTest.testKeys2` structural control (#51). The original Java
aggregate suites exclude this class. The original controls and Java failure
messages are retained, rather than rewritten to match Rust's output.

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
remove nothing. The string automaton lacks U+FFFE and U+FFFF, which anyURI
values may contain (it lacked the supplementary-plane characters too before issue
#17), so it is no longer used when the patterns admit one; the enumerating
fallback counts those values instead. The regressions cover the remaining values,
cardinality and distinct-value assignment.

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

Issue #17 was the same gap for strings. The value space of rdf:PlainLiteral holds
the strings and the pairs of a string and a lowercase language tag
(rdf:PlainLiteral §3); xsd:string and its subtypes hold strings only. It was
counted from the positive length facets, so `xsd:string[length 0]`, which holds
only the empty string, still held one value once `""` was excluded
(`RDFPlainLiteralTest.testSize_3`). The string value space now follows HermiT's
`RDFPlainLiteralDatatypeHandler`. A restriction of xsd:string or rdf:PlainLiteral
with length facets only is a pair of length windows, one of strings and one of
tagged pairs; any other restriction is an automaton over the strings and their
tags. It intersects the positive restrictions, subtracts each negated string
restriction, then the excluded values that remain. The emptiness check, the
cardinality and the distinct-value assignment all use it. This also corrected
three other answers. Restrictions to three different lengths were consistent. A
pattern on rdf:PlainLiteral held only its strings, not their tagged pairs, so two
distinct values of `rdf:PlainLiteral[pattern "a"]` clashed. And a restriction with
a large `maxLength` was built as an automaton, in quadratic time:
`xsd:string[maxLength 100000]` did not finish within 20 seconds.

Four corrections deviate from Java; no Java case depends on them. Language tags
are case-insensitive, and the value space holds them in lowercase
(rdf:PlainLiteral §3), so `"x"@en` and `"x"@EN` are one value; Rust, like
HermiT's `RDFPlainLiteralDataValue`, compared them as written, so a functional
data property with both values clashed. rdf:langRange matches a tag under the
extended filtering of RFC 4647 §3.3.2, as rdf:PlainLiteral §3 requires; HermiT
uses basic filtering, so `de-DE` did not match `de-Latn-DE`. The example in the
specification follows basic filtering, which OWL 2 erratum 7 records as an error.
The string automata now have every XML character (XSD 1.1 Part 2 §3.3.1), `#xD`,
`#x80`–`#x9F` and the supplementary characters included. Rust's lacked them, so
`xsd:string[pattern "\r"]` was empty, and HermiT's length and language-range
automata lack them too. And HermiT turns the length windows of a subset into an
automaton by intersecting the windows' automata, not uniting them, so conjoining
a pattern with a subset that has a window of strings and one of tagged pairs,
such as that of `rdf:PlainLiteral[minLength 1]`, leaves nothing.

String lengths still count UTF-16 code units, as HermiT's do, while XSD 1.1
counts characters (Part 2 §4.3.1), so a supplementary character has length 2.
The count of a length window follows HermiT and XSD, one value per sequence of
characters. Correcting the lengths is left to a separate change.

Issue #31 was a gap in the disjointness of datatypes. rdf:XMLLiteral is
disjoint from every other datatype of the OWL 2 datatype map: OWL 2 Structural
Specification §4.8 takes it from RDF Concepts §5.1, whose XML values are
disjoint from the value space of every XML Schema datatype and from the strings,
and owl:real, owl:rational and rdf:PlainLiteral hold numbers, strings and pairs
of a string and a language tag. The emptiness check of a fresh value kept its
own list of datatype families, which lacked rdf:XMLLiteral, so a value of both
rdf:XMLLiteral and xsd:boolean was taken to exist (`XMLLiteralTest.testRange_3`).
The emptiness check and the count now read one disjointness test, which follows
HermiT's `DatatypeRegistry.isDisjointWith` and already had rdf:XMLLiteral.
rdf:XMLLiteral has no facets, so its value space holds every XML literal,
infinitely many, unless rdf:XMLLiteral is negated. The complement of another
datatype within the data domain holds every XML literal. Fixed XML literals
were already checked correctly.

Issues #18, #22, #23, #24, #25 and #27 had one cause, in the property
classifiers. They read a role's subsumers off the role labels of one model edge,
but the absence of a label does not establish non-subsumption. The role automata
enforce a role chain or transitivity by propagating universal restrictions, not
by adding edges, so `s1 ⊑ s2`, forced by `s1 ∘ r ∘ r⁻ ⊑ s2` and `⊤ ⊑ ∃r.⊤`,
left no `s2` label (#22; #24 adds transitivity and symmetry). A subsumption
forced by nominals (#23), by equal data values (#18, #25) or by a one-element
domain (#27, where a role holds every pair) left none either. The classifiers now
follow HermiT's `classifyObjectProperties` and `classifyDataProperties`. Each
role R gets a proxy concept `∃R.M`, for a fresh concept M with an instance, and
each data property P a proxy `∃P.U`, for a fresh unknown datatype U; the top
and bottom properties are owl:Thing and owl:Nothing. R ⊑ S holds exactly when
the proxy of R is subsumed by that of S: if a model has R(x, y) but not S(x, y),
interpreting M (or U) as {y} separates the two proxies, and since M has an
instance, a role that holds every pair has a proxy equivalent to owl:Thing. The
ontology is clausified once with the proxy definitions, and the concept
classifier classifies the proxies, mirroring every subsumption onto the inverse
roles as HermiT's `QuasiOrderClassificationForRoles` does. Before, each
subsumption test of the non-deterministic path clausified the ontology twice.
U also needed HermiT's unknown-datatype semantics: the tableau keeps the values
of U apart from those of its negation, and the datatype checker ignores both.
Rust kept them apart only in the `ignoreUnsupportedDatatypes` mode, and its
checker excluded every known value from an unknown datatype; both now follow
HermiT, whenever the ontology has an unknown datatype. The regressions
check each hierarchy, pair by pair, against the separate subsumption tests
(`isSubObjectPropertyExpressionOf`, `isSubDataPropertyOf`) under the default,
core-blocking, individual-reuse and quasi-order configurations.

The fix also resolved #20 and #13. `SubObjectPropertyOf(owl:topObjectProperty
op6)` makes `op6` and its inverse hold every pair, so `printHierarchies` must
print them as equivalent to owl:topObjectProperty, but Rust printed them as its
sub-properties (`ReasonerTest.testHierarchyPrinting1`); the rest of the
expected hierarchy also follows from the fixture's axioms. Individual-reuse
classification of Dolce (#13) ran out of memory in the object-property
classifier, which built its models with a reasoner of the default
configuration instead of the requested one. Under the default creation-order
strategy its first Dolce model kept expanding: the resident set grew from
54 MiB after the classes to 1.2 GiB about a minute later, before that model
was complete. This was the expansion of one model under the wrong strategy,
not allocations retained across tests. The proxy classifier builds every
tableau under the requested configuration, and the case now passes in about
70 seconds, within its 120-second deadline, with a peak resident set of 75 MiB.

Three changes keep the proxy classification fast. Without worker threads, the
quasi-order classifier builds one model at a time and harvests it before it
chooses the next concept, as HermiT's serial loop does, rather than rounds of
up to 256 models, many of which an earlier model of the round made unnecessary;
`ClassificationTest.testWine` takes about 6 seconds instead of 10. The
unknown-datatype phase walks only the assertions of the last round, as
HermiT's does, rather than every assertion. On Horn ontologies an inverse role
takes the inverses of its role's subsumers instead of a model of its own. A
proxy's model is larger than one edge, and in an ontology with nominals every
proxy test loads the ABox, as HermiT's does, so the object properties of Galen,
and of Wine under individual reuse, take one to six seconds longer to classify
than the edge read-off did.

Issue #26 was a gap in the lookups of the object-property hierarchy. Under the
OWL 2 Direct Semantics owl:topObjectProperty holds every pair of elements and
owl:bottomObjectProperty none (§2.2), and `ObjectInverseOf` swaps the pairs of
its property (Table 1), so each of the two is its own inverse. HermiT's
`Reasoner.H` resolves `ObjectInverseOf(owl:topObjectProperty)` and
`ObjectInverseOf(owl:bottomObjectProperty)` to the properties themselves
(`AtomicRole.getInverse`). The classification already gave the inverses that
meaning, but the hierarchy, which has no node for them, looked them up as fresh
properties, between its top and bottom nodes. So the sub-properties of
`ObjectInverseOf(owl:bottomObjectProperty)` were owl:bottomObjectProperty, not
none (`ReasonerTest.testSubProperties`, operation 13), the super-properties of
`ObjectInverseOf(owl:topObjectProperty)` were owl:topObjectProperty, and each
inverse was equivalent only to itself. The hierarchy now looks each inverse up
as the property itself, in every sub-, super- and equivalent-property query,
direct or not, and so in `getInverseObjectProperties`; as in Java, no node
lists the inverses.

One correction deviates from Java; no Java case covers it.
`getDisjointObjectProperties` of `ObjectInverseOf(owl:bottomObjectProperty)`
now returns every property, as for owl:bottomObjectProperty, because the empty
role is disjoint from every role (Table 6). Java tests
`isOWLBottomObjectProperty()`, which does not unwrap the inverse, and so
searches the hierarchy below owl:topObjectProperty with the atom `bottom(a, b)`.
That atom clashes only when the ontology mentions owl:bottomObjectProperty, the
only case in which it is axiomatized, so Java returns the bottom node alone, or
every node except the top node.

The other queries that take an object property expression already answered
alike for the inverses and the properties: the subsumption, equivalence,
inverse and disjointness entailments, property chains, the property
characteristics, domains, ranges and instances. Each reduces the query to a
test ontology, whose clausification gives the inverses their meaning, or to
role atoms or pairs, whose direction does not matter for a built-in property.
The regressions compare each of these queries on the two inverses with the
same query on the properties, over ontologies that mention the built-in
properties, their inverses or neither. They also check the hierarchy lookups
under the default, core-blocking, individual-reuse and quasi-order
configurations, and against the separate subsumption test.

Issue #19 was a gap in the direct types of individuals. Under the OWL 2 Direct
Semantics the types of an individual are closed under subsumption, so its direct
types, the most specific ones, are the types none of whose strict subclasses is
a type, and owl:Thing is a direct type only of an individual with no other type.
The instance manager keeps each known instance at the most specific node that
records it, and its direct filter dropped a known node only when a child of the
node was known too. In `ReasonerTest.testDirect`, `:a` is an instance of `:C`,
below `:B`, by either disjunct of each of its assertions, since `:Cp` is empty
and `:D` and `:E` are subclasses of `:C`. It becomes a known instance of `:C`
only when `realize` confirms the possible instance that `:D` or `:E` pushes up,
and owl:Thing, which records every individual, has `:B` as its child, not `:C`.
So owl:Thing stayed a direct type beside `:C`. The known nodes are now closed
under ancestors first, and the direct types are the minimal nodes of the closure.

`realize` had two more gaps, which it shares with Java's. It visited the nodes
breadth-first upward from the bottom node and stopped at a node without
instances. So a possible instance refuted along a long path could reach a node
already visited from a shorter one, and a node above nodes without instances
was never visited; either way the possible instance was never tested. Java tests
such leftover possibles when a query reaches them, but the Rust queries read the
known instances only, so the type was lost, direct or not: with
`ObjectUnionOf(:X3 :Z3)(:a)`, both three levels below `:P`, and `:Y(:b)`, one
level below it, `:a` was no instance of `:P`. `realize` now visits every node
after all of its children, so each possible instance is tested at every node it
reaches. `getInstances`, direct or not, and the realization read the same known
instances, and are corrected with `getTypes`.

One correction deviates from Java; no Java case covers it. With `:A(:a)` and
`ObjectUnionOf(:F1 :F2)(:a)`, where `:F1` and `:F2` are subclasses of `:D`, three
levels below `:A`, and `:A` has a leaf subclass `:G`, the pinned Java checkout
returns both `:A` and `:D` as direct types of `:a`, although its
`getInstances(:A, true)` leaves `:a` out. Its breadth-first `getTypes` reaches
the known `:A` from `:G` before it confirms `:D`. Rust returns `:D`. The generic
`InstanceManager`, which the reasoner does not use, ports that traversal; it
now visits the nodes in the order `realize` does.

The regressions check `getTypes`, the realization and `getInstances`, direct and
not, under the default, core-blocking and individual-reuse configurations,
against separate tests of each type and each subsumption. They cover the Java
fixture, both `realize` gaps, the deviation above, owl:Thing, a class
equivalent to it, an unsatisfiable class, equivalent and incomparable types,
equality and nominals. The pinned Java checkout gives the same answers, except
in the deviation above.

Issue #21 was a gap in the printed hierarchies of inconsistent ontologies.
Every OWL 2 ontology implicitly declares owl:Thing, owl:Nothing and the top and
bottom object and data properties (OWL 2 Structural Specification §5.8, Table
5), so declaring one is redundant, and HermiT's `HierarchyPrinterFSS` declares
none: its `needsDeclaration` compares each element with the built-in constants.
An inconsistent ontology entails every axiom, so each of its hierarchies is one
node, both the top and the bottom node, which the top element represents. The
Rust printers took the built-in entities to be the representatives of the top
and bottom nodes, so the class printer declared owl:Nothing
(`ReasonerTest.testHierarchyPrinting3`). The property printers also compared
with the built-in IRIs, so they declared nothing more, but those of
`printHierarchies`, like the dumpers, sorted the bottom element among the other
members, whereas HermiT's comparators put it first. A hierarchy now keeps the
top and bottom elements it is built with, and `transform` maps them too; every
printer and dumper compares with them, for classes and properties alike. Java
is right here: the expected `hierarchy-printing-3.txt` stands, and nothing
deviates from Java.

The regressions print the hierarchies of inconsistent ontologies with and
without properties and inverse roles, and of a consistent ontology whose
built-in entities share their nodes with other entities, under the default,
core-blocking and individual-reuse configurations. Exactly the entities that
are not built in are declared, each hierarchy of an inconsistent ontology is
one equivalence led by its bottom and top elements, and a printed class
hierarchy, read back, prints the same. The pinned Java checkout prints the same
axioms for each of these ontologies.

Issues #32 and #33 were obsolete fixtures, not Rust defects. Both
`BlockingValidatorTest` scenarios build a tableau by hand and hang the nodes
that should block or be blocked (a1, a2, b1, b2, b3) directly off NI roots.
Both ontologies use the inverse role `INVR`, and with inverse roles HermiT's
`ValidatedSingleDirectBlockingChecker.canBeBlocker` and `canBeBlocked` accept
a tree node only when its parent is a tree or graph node: a child of a named or
NI node can feed its label back to that node, so it must not be blocked. The
pinned Java checkout therefore fails both tests at their first blocking
assertion, before any validator assertion runs, and Rust ports the same rule.
The upstream source stays unchanged under `upstream/`; the corrected copy in
`corrected/java/org/semanticweb/HermiT/tableau/BlockingValidatorTest.java`
only makes the old roots a and b tree children of one fresh NI root r that has
no labels or edges. a and b keep their labels and edges and, as children of an
NI node, still can neither block nor be blocked, so every assertion keeps its
meaning; none is changed. `port_blocking.py` now ports the corrected copy.
Every assertion passes in Rust and, compiled against the pinned checkout, in
Java. The validator results also follow from the labels: in the annotated
equality scenario, a2 is `B` and has the `R`-neighbour a in `C`, so as a copy
of a1, whose `R`-successor a11 is in `C`, it would have two `R`-neighbours in
`C` against `B <= <=1 R.C`, and the block is invalid. In the other scenario, b2
and b3 are both `R`-successors of the `C` node b and would both copy a1's `D`
against `C <= <=1 R.D`, so exactly one of their blocks is valid; the blocks of
a2, a111, b1 and a121 respect every clause. Nothing deviates from Java's
blocking or validation; only the fixture changed.

Issue #34 was a missing description-graph context in the SWRL clausifier. In
the description-graph formalism (Motik et al., "Representing Ontologies Using
Description Logics, Description Graphs, and Rules", AIJ 2009), rules over graph
properties range over every graph vertex, including the anonymous vertices of
a graph instance, while the other rules stay DL-safe. Rust guarded every rule
variable with `internal:named`, so in `graph.GraphTest.testGraph2` the rule
deriving `conn` never matched the anonymous graph under `:A`'s `:T`-successor
and `A <= B` was missed. The clausifier now takes the description graphs and
ports `NormalizedRuleClausifier.processRules`: a rule over graph properties is
unguarded, a property used only in rules takes the kind of its rule's other
properties, iterated to a fixpoint, and every other rule, including every rule
of an ontology without graphs, keeps its guards. Graph properties in OWL
axioms and rules that mix both kinds are rejected, as in Java. The native test
now clausifies through this path rather than adding start clauses by hand.
Regressions check that a graph rule fires on an anonymous vertex while a
DL-safe rule over an ordinary property does not, the kind inference for
rule-only properties, and the rejections. Nothing deviates from Java.

Issues #35 to #44 and #46 were obsolete structural controls, not clausifier
defects. The pinned Java checkout fails all eleven. The `ClausificationDatatypesTest`
controls spell every integer as `xsd:int` and `xsd:string` literals as plain
literals, as an older HermiT printed them. Current Java and Rust print the
literals as written: in `testDataComplementOf3`, for example,
`"5"^^xsd:nonNegativeInteger` and `"5"^^xsd:integer` where the control has
`"5"^^xsd:int` twice. The controls also list enumerations in Java's hash order.
`testExistsSelf1` numbers its two fresh `def:` predicates the other way round. The
structural runner now compares printed clause sets semantically
(`tests/support/clause_compare.rs`). Under OWL 2 and XSD 1.1, a literal whose lexical form is
valid for its datatype becomes one key per data value: `"18"^^xsd:int`,
`"18"^^xsd:integer` and `"18.0"^^xsd:decimal` are the same number, and a plain
literal without a language tag abbreviates `xsd:string`. Enumerations and clause
heads and bodies compare as sets. One bijection renames the fresh `def:`,
`defdata:`, `nnq:` and `all:` predicates, each within its own family, across all
clauses and facts together. Everything else must match exactly: ordinary and
nominal names, variables, negation, numbers, clause count and direction,
distinct value spaces such as `xsd:double` against `xsd:decimal`, and ill-typed
literals. Unit tests show that the comparator still rejects different values,
ill-typed literals, an inconsistent or cross-family renaming, and every other
structural change. When the comparison fails, the runner still reports the literal
set difference. The Rust clauses were checked by hand against each input: for
example, `A <= all dp.not(D1 and D2)` yields `dp(X,Y) -> defdata:0(Y)` and
`defdata:0 <= not D1 or not D2`. In `testExistsSelf1`, `a` is in `def:1 <= exists r.Self`
and in `not def:0`, where `exists r.Thing <= def:0`, which matches the input
assertions `a: exists r.Self` and `a: all r.Nothing`. The upstream traces are unchanged
and need no correction, because each control is semantically equal to the
clauses. Nothing deviates from Java's clausification.

Issues #45 and #47 to #50 were obsolete `ClausificationTest` controls as well;
the pinned Java checkout fails all five. Run on the same fixtures, it prints
exactly Rust's clauses. Three spellings differed, none of them a clausifier defect:

- The fixtures are RDF/XML resources whose ontology IRI is
  `file:/c:/temp/test.owl` (the wine IRI for `testNominals4`). Java's
  `getDLClauses` declares that IRI plus `#` as the default prefix, and a `nom:`
  prefix for the namespace of the individuals. The recorded snapshots drop the
  ontology header, and the runner declared `file:/c/test.owl#` and no `nom:`
  prefix. It now recovers the ontology IRI from the upstream test and fixture
  (`AbstractOntologyTest.ONTOLOGY_IRI` for `loadOntologyWithAxioms`) and declares
  the prefixes as Java does.
- Current HermiT names nominal variables `Z`, `Z1` where the controls have `Y`,
  `Y1`. Each clause is universally closed, so a bijective renaming of its own
  variables is the same formula. The comparator now takes, per clause, the least
  rendering over all bijections of its variables onto fresh names. Merging
  variables, replacing one by a name, swapping the arguments of a role, or moving
  an atom to another clause is still rejected, and unit tests show it.
- `testBasic` encodes `exists r.(exists s.c) <= d` with transitive `s`. The
  control's automaton has two states and five clauses; since the issue #8
  construction, HermiT and Rust use four states and nine clauses. The clauses
  that derive `all:` states are a monotone definition, so each state holds
  exactly where the words it accepts lead to its final concept. The comparator
  replaces every state by the minimal DFA of its language, when both sides use
  states only in that form, and compares the remaining clauses exactly. Both
  encodings give `def:0` the language `s s* c`: `def:0` contains `exists s.c`
  and, by the transitivity of `s`, nothing more. Unit tests reject a missing
  loop (`s c` only), `s* c` (which would wrongly entail `exists r.c <= d`),
  another role, the inverse role and another final concept.

The Rust clauses were checked by hand. `testNominals1` has
`c(X) -> r(X,i1) or r(X,i2)` through the nominal concepts, and
`d <= atLeast 1 s.not def:0` with `def:0(i1)`, `def:0(i2)`. Besides those
facts, `def:0` occurs only negatively, so its least extension `{i1, i2}` is the
one that matters and the clause says `d <= exists s.not {i1, i2}`. `testNominals2` bounds
`all r.{i1, i2}` by equalities, `all r.not {i1}` and `all r.not {i1, i2}` by
clauses with empty heads, and keeps the `atMost 2` clause unchanged.
`testNominals3` turns the successor into a predecessor, and `testNominals4` gives
`Chianti` the `hasSugar` value `Dry`. The upstream traces are unchanged. Nothing deviates from Java's
clausification.

The commands and regeneration procedure are in [README.md](README.md). Tests
run serially in CI; isolated Java workers have a 120-second deadline and 512 MiB
allocation budget. These are Rust allocation limits, not a limit on all operating
system memory or on any external VM. Java trace generation uses `-Xmx256m`.
