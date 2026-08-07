# Cross-color common-span reuse gate

## Question and review selection

Experiment 0053 left a `20 > 13` Hall deficiency containing all fourteen
cap/cup rank-three crossing obligations in the alternating ten-point root. A
bounded route review compared containment-minimal proof reuse, merging cap and
cup obligations with identical endpoints, and a conserved tree-global charge.
The evidence packet SHA-256 was
`9d017fc6059f3c4caaf6ec59b8bf4739eb76928904589163363c587127b7321c`.
Sol rated the review `partially_supported` with high confidence and selected
the common-span quotient as the sharpest next falsifier. Fable returned zero
tokens at its provider usage limit, so no Fable judgment or consensus is
claimed.

The frozen gate merges only the seven cap/cup rank-three pairs having the same
endpoint span. A merged charge keeps the intersection of the two candidate
families, because a slot must be valid for both original obligations. All
other exclusive genealogy charges remain unchanged. Success required both a
perfect matching and a semantic theorem showing why one published resource
pays the two child increments.

## Computational result

The candidate graph passes. The seven common spans are

    (0,3), (1,4), (2,5), (3,6), (4,7), (5,8), (6,9).

Merging their cap/cup copies reduces the 27-charge graph to 20 charges. The
intersection candidate families admit an explicit perfect matching of size
20, independently replayed using cell-mask and row-height representations.
Thus the old `20 > 13` Hall witness is removed at the graph level.

This positive matching result is not a proof resource. For every common span,
the exact-ray normal form places the cup ray in the lower child and the cap ray
in the upper child. The child supports are disjoint. More decisively, the
proposed one-coefficient payoff is already arithmetically false at this gate:

    decomposableThreshold 7 4 7 + decomposableThreshold 4 7 7 = 32,

while

    decomposableThreshold 7 3 7 + decomposableThreshold 3 7 7
      + choose(5,2) = 22.

The missing amount is ten, exactly a second rank-three Pascal coefficient.
Sharing endpoint labels therefore does not make the two published child
increments into one cost.

## Lean result

`StructuralChargingCrossColorReuseCounterexample.lean` proves, without
`sorry`, `admit`, unsafe axioms, or external oracles:

- the seven recorded spans are genuine members of both the cap and cup exact
  rank-three crossing frontiers;
- retained published cores in disjoint children are disjoint;
- the type of a nonempty retained subset contained in both cores is empty; and
- the concrete single-coefficient inequality above is false (`32 > 22`).

The Python certificate is reproducibility support for the repaired 20/20
matching. The semantic and arithmetic refutations are kernel-checked Lean
theorems.

## Disposition

Common endpoints alone are retired as a proof-reuse rule. The result does not
exclude a stronger nonadditive geometric invariant whose payoff is different
from the sum of the two published child increments. Containment-minimal
frontiers remain parked because containment has not been shown to imply
semantic payment. The next design target is therefore a genuinely conserved,
branch-indexed tree charge. It must name its owned retained object, prove
nonreuse across tree addresses, and pass both the three-vertex local/global-gap
counterexample and this ten-point witness before any new Hall theorem is
attempted.

## Reproduction

    python3 scripts/produce_cross_color_common_span_gate_k7_n10.py \
      --output data/derived/e3-cross-color-common-span-gate-k7-n10.json
    python3 scripts/check_cross_color_common_span_gate_k7_n10.py \
      data/derived/e3-cross-color-common-span-gate-k7-n10.json
