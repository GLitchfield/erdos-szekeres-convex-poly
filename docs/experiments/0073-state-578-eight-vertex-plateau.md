# Experiment 0073: state-578 eight-vertex plateau

Date: 2026-08-09

Status: Outcome 1 for the local target; global state-578 closure remains open

## Question

Does every decomposable eight-vertex carrier in which every five-subset
contains a four-cup necessarily contain a five-cup? If so, can the result be
reconnected to the exact eight-vertex remainders at the `32 = 24 + 8` gate?

## Result

Yes. `StructuralChargingNextState578EightVertex.lean` proves the stronger
root-only theorem `eightVertex_deepSplit_denseFourCups_force_cupFive`. It
needs only one nonempty `HasDeepBelowSplit` partition of an eight-vertex
carrier; recursive decomposability below that split is unnecessary. The
selected theorem `eightVertex_decomposable_denseFourCups_force_cupFive`
follows by exposing the root of a decomposable carrier.

Together with the previously compiled eight-vertex hypergraph equivalence,
Lean now proves
`eightVertex_decomposable_fourCupFamily_has_threeTransversal_or_cupFive`:
every decomposable eight-vertex carrier contains a five-cup or admits a
three-vertex transversal of all four-cups.

All statements compile without `sorry`, `admit`, generated finite
certificates, or an external oracle. The axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Root-profile proof

The proof treats the seven possible nonempty root profiles.

- `1+7`, `2+6`, and `3+5`: choose a non-cup four-set in the upper child and
  adjoin one lower vertex. Any forced four-cup would use at least three upper
  vertices, contradicting the deep-split endpoint bound.
- `5+3`: a lower four-cup traps all three upper vertices strictly between its
  sweep endpoints. Density then forces a crossing cup whose upper vertices
  are both interior points and required sweep endpoints.
- `6+2`: the same endpoint trap uses one additional internal cup vertex. If
  the forced cup drops an endpoint, it must use both upper vertices, and the
  nearer one is again an impossible interior endpoint.
- `4+4`: density produces two upper vertices bracketing the complete lower
  child and also produces a lower cup triple. Their union is a five-cup by
  the crossing-color law.
- `7+1`: split the lower child into vertices below and above the unique upper
  vertex. A side of size at least five gives an endpoint extension. Otherwise
  a non-cup balanced `2+2` set directly contradicts density; if every balanced
  `2+2` set is a cup, a three-plus-two gluing lemma constructs a five-cup or a
  five-set containing no four-cup.

This conceptual proof independently explains the bounded census. The two
enumerators' earlier count of 186,888 decomposable colorings remains advisory
evidence, not part of the Lean theorem.

## Exact `24+8` reconnection

Under five-cup avoidance, Lean constructs a three-vertex four-cup boundary on
each exact eight-vertex remainder currently present at state 578:

- the remainder outside the six-cap saturation;
- the remainder outside the original three-cup/three-cap packing; and
- the remainder outside the protected one-cup/five-cap packing.

These are genuine global-state consequences because decomposability descends
to each nonempty remainder and the existing packing theorems prove its
cardinality is exactly eight.

## Limitation and next target

The local plateau is closed, but the full residual anchor plateau is not.
Each new boundary hits four-cups contained wholly in the unused eight
vertices. The residual cups driving the private-star exchange can cross the
selected 24-vertex support, so no existing theorem proves that the remainder
boundary hits them. The next consumer must couple such a crossing residual cup
to the six-cap address matrix or prove that it leaves a four-cup trace inside
the unused remainder. Without that bridge, the three-boundary cannot yet fill
`FullSpineResidualBoundary578` or produce the forbidden nine-transversal.

Thus this batch is **Outcome 1 for its selected local theorem** and a major
structural advance, while the route-level state remains **Outcome 2** until
the crossing-to-remainder bridge or another global exchange is proved.

## Formal evidence

- `ErdosSzekeres/StructuralChargingNextState578EightVertex.lean`
- `lake build ErdosSzekeres.StructuralChargingNextState578EightVertex`
- `make test`
