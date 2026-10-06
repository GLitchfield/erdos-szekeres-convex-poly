# Finite history certificate candidate

The open scope question is whether the literal k6 context SSS1L3L2LS,
maxima111 at globals(5,5,6), occurs along a genuine decomposable coloring
history with root avoidance. The existing Satisfies theorem constrains only
four internal vertices and does not certify external ancestry.

Probe20261002-144048-b98707 checks one explicit tree, without enumerating a
class. On Fin7 assign levels [0,0,0,1,3,2,0]. On an increasing triple with
at least one external vertex, its largest level determines the ancestor
split; the color is left iff the middle vertex has smaller level. An
all-level0 triple is right. This is precisely the crossing rule for lower
child and upper singleton siblings. Internal core is [0,1,2,6].

The six splits (lower | upper) are:

* [0,1,2,3,5,6] | [4] at the root;
* [0,1,2,3,6] | [5];
* [0,1,2,6] | [3];
* [6] | [0,1,2];
* [2] | [0,1];
* [1] | [0].

The shared classifier confirms every crossing, all127 nonempty subsets,
maximum(cap,cup,strong)=(4,4,5), and the one-change law. Its separate
consecutive-chain/profile and strong-size implementations agree on the maxima.
These are diagnostics, not Lean credit. Repeated Context.part from the seven
child root, keeping the first three lower sets with maximum1, gives the literal
word/maxima. Each sibling is singleton, so its actual cap maximum is1.

A future single-node finite statement should certify the three ancestor deep
splits, root decomposability and subset cap/cup<=4 / strong<=5, core all-right,
and the literal root-part equality with actual singleton chain maxima. Existing
IsDecomposable.isSweepRealizable then supplies geometric coloring realization;
it does not assert IsGeometricallyDeepBelow for the same coordinate tree.
The registered statement includes Satisfies. Prove it by applying the already
closed ctx_satisfies_of_deepBelowSplit three times, starting from root Satisfies
given by the finite root-avoidance certificate. Literal positionsOf checks
identify the three keep lists; actual singleton chain maxima are 1. This reuses
the existing interpretation theorem rather than duplicating endpoint checks.

This is easier than general feasible PEEL for a structural reason: the full
coloring is forced by three singleton ancestor splits and a constant-right core.
Only35 triples and128 subsets are involved; no recursive context-bound reduction
or unknown selection invariant is needed. It removes a documented scope question
for the cost/end example and is not another sibling-penalty narrowing.

Actual child cardinality is4. A history certificate will not construct an
8-point child set, prove tightness of bound8, prove general singleton attainment,
or advance the happy-ending theorem by itself. Exact-k6 recurrence certification
is now closed and pinned at commit1cd0281b18dddb1177d47d876c1e6b87f15fc741,
receiptf2d86d2b78a2888f86ed602b7adc5c32e04d850e5616102b720b5348c4a89c38.
History registration job20261002-152751-e1af40 succeeded (103.6s/2305MiB);
ctx_k6_actual_history_witness has locked type hash80c84048681897f7 and a live claim.

Library/source reuse: decomposable.coloring-enumeration;
research.context-part; scripts/decomposable_context_functions.py (split checker
and all-triple subset classifier); scripts/enumerate_decomposable_colorings.py
(chain profiles, strong sizes, one-change). es search for seven-vertex actual
context history returned no theorem; K6-HISTORY.search.json is exact.
