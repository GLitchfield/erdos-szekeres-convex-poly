# Decomposable realization bridge review

Date: 2026-08-03

Status: advisory review complete; Lean theorem independently kernel-checked.

## Reviewed claim

The bounded package asks whether every coloring satisfying the repository's
abstract `IsDecomposable` predicate is induced by a genuine
`SweptConfiguration`, including decompositions whose two children interleave
in sweep order.  The route interpretation is intentionally negative: this
would close the abstract-versus-realizable coloring boundary, not repair the
failed pair-rank transition or prove the uniform `2^(k-2)` count.

The compiling endpoint is
`IsDecomposable.isSweepRealizable : IsDecomposable χ →
IsSweepRealizable χ`.  Its induction uses `FixedXRealizesOn.deepBelowMerge`,
which retains the global abscissae `x_i=i` and chooses one finite bound for
opposite vertical shifts of the child ordinate functions.

## Provider review

The blind, zero-critique-round review used Claude Fable 5 and Codex Sol
(`gpt-5.6-sol`).  The evidence packet SHA-256 was
`98e8213b03d9aa12146c2690d7fad234d8e4a76da0cb65089df46fabd87fe706`.
The reviewed `DecomposableRealization.lean` had SHA-256
`99b4e76d0db2e933f2e51163a859e1efe2c4d5c7cc2ba24c7314198abae549bd`;
the only post-review edits to that file were scope clarifications in comments.
Both reviewers returned `partially_supported`: Fable at medium confidence and
Sol at high confidence.

Both reviewers independently supported the exact displayed implication,
checked that `HasDeepBelowSplit` has no contiguity premise, recomputed all six
crossing determinant signs, and agreed that the result forecloses rather than
repairs a realizability-sensitive pair-rank transition.  Neither found a
mathematical counterexample or a missing case in the merge.

## Objection disposition

1. The packet omitted `orientation`, `exists_strictUpperBound_of_finite`, and
   `generalPosition_of_ordered`, and contained no build transcript.  The first
   is the determinant in `Basic.lean`; the latter two compile in
   `Composition.lean`.  A full `make test` built 9,630 Lean jobs, passed 43
   Python tests, and replayed the repository certificate checkers.  The final
   theorem's axiom audit contains only `propext`, `Classical.choice`, and
   `Quot.sound`.
2. Equality of the induced coloring does not prove that the constructed
   coordinates witness the identical recursive tree through the stronger
   `IsGeometricallyDeepBelow` predicate.  That stronger statement is not
   needed for `IsSweepRealizable` and is now excluded explicitly from the
   source comments, README, survey, plan, and Wayfinder claim.
3. The next higher-order correlation state is still unspecified.  No uniform
   route is selected by this milestone.  A candidate must define a finite
   carrier, separate the existing realizable collision, compose under every
   interleaved split, and have a state-count bound depending only on `k` before
   it becomes a proof route.

The review is advisory.  The completed Lean proof, not reviewer agreement, is
the mathematical evidence for the bridge.
