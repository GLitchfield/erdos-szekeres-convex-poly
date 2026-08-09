# Experiment 0074: state-578 crossing-row consumer

Date: 2026-08-09

Status: compiling child-capacity bridge; address-only closure refuted

## Question

Can the residual four-cup which crosses the selected six-cap support and
evades the unused three-boundary be consumed at the full residual matrix's
common minimum?

## Compiling results

`StructuralChargingNextState578CarrierMatrix.lean` now proves the exact
full-family analogue of the sampled cap-localization theorem. At a common
minimum in the tight one-spine branch, one of four alternatives holds:

1. all six cap blocks lie in the lower child, which has at least 24 vertices;
2. all six cap blocks lie in the upper child, which has at least 24 vertices;
3. one complete cap column remains at the minimum address; or
4. the distinguished four-owner spine row remains at the minimum address.

The same file proves the complementary child has at most eight vertices in
either localized branch. `StructuralChargingNextState578EightVertex.lean`
then transfers decomposability and global five-cup avoidance to that child and
constructs a three-vertex boundary hitting every four-cup wholly contained in
it.

The strict-address branch has also been sharpened. If the six-cap support is
in one child, every residual row is either wholly contained in that large
child or all six cells of the row equal the common-minimum address. Every base
cell retains the exact cup-endpoint, cap-endpoint, or reverse-separated
trichotomy of its first joint split.

All these declarations compile. Their axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`.

## Kernel-checked negative control

`StructuralChargingNextState578CrossingRowCounterexample.lean` gives an exact
32-vertex finite-set model with:

- a 24-vertex selected support and an eight-vertex unused complement;
- a 27-vertex large child containing the selected support;
- a five-vertex small child;
- and a four-set meeting both selected and unused supports while remaining
  wholly inside the large child and disjoint from the small child.

A second theorem gives a two-row, six-column all-base address matrix satisfying
the bare row/column prefix and common-minimum contracts. These results use
`decide`, not `native_decide`, and audit to only the standard Lean axioms.

This is deliberately a relaxed set/address model, not a triple coloring. It
does not refute an endpoint- or color-sensitive consumer. It does prove that
crossing the selected `24+8` support partition is not the same as crossing the
common-minimum decomposition split. Therefore the new small-child boundary
need not hit the packaged crossing cup.

## Independent agent audits

The frozen read-only Laplace audit validates the four-way localization theorem
and independently derives the large-child-or-base-row repair. It recommends
retaining base-cell endpoint shapes and using two cap blocks disjoint from a
four-set. Its all-base examples show that addresses alone cannot close the
route.

The frozen Mathematical Innovation Scout proposes three collective
replacements. Its preferred bounded candidate is a 24-row cap-vertex-deletion
ledger. For each of the four vertices in each of the six cap blocks, density
chooses a residual cup avoiding the other three vertices. Within a column,
either one chosen row avoids the entire cap block or the four rows are
distinct. This uses all six cap blocks and creates endpoint-bearing witnesses
instead of six independent pair classifications.

Both audits are proposals, not proofs. A bounded Sol/Fable review is pending
before the deletion ledger is selected as the next main invariant.

## Next decision

The provider review must compare three exact continuations:

1. the six-cap vertex-deletion residual ledger;
2. boundary swaps which expose private blocking cups on the unused eight;
3. a common-cap path which charges each residual row at its first exit.

The selected candidate must have a cheap falsifier and a first compiling Lean
theorem. Address-only plateau elimination is expired. The route-level state
remains **Outcome 2**: substantial compiling progress, with a sharply reduced
but still open endpoint/incidence obstruction.

## Formal evidence

- `ErdosSzekeres/StructuralChargingNextState578CarrierMatrix.lean`
- `ErdosSzekeres/StructuralChargingNextState578EightVertex.lean`
- `ErdosSzekeres/StructuralChargingNextState578CrossingRowCounterexample.lean`
- `lake build ErdosSzekeres.StructuralChargingNextState578EightVertex`
- `lake build ErdosSzekeres.StructuralChargingNextState578CrossingRowCounterexample`
