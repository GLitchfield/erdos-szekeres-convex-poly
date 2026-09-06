# 0122 — Lean mapping of the context induction (Workstream B)

**Date:** 2026-09-06.  **Depends on:** 0117 (union lemma), 0118 (depth-one closed
form), 0120 (recursion), 0121 (interval cuts, additivity tests).

## What was formalized

`ErdosSzekeres/DecomposableContext.lean` (core, commit d88e3d4) defines contexts
(`Ctx.Context`: parameters, sweep word over `child` / `ext level side` letters,
sibling maxima), the chain and join extensions, `cupLimit` / `capLimit`, the
interval-cut recursion `bound`, `Satisfies χ S σ`, `part`, `positionsOf`,
`withMaximum`, `WellFormed`, and `chainMax`.  Its `#eval` values agree with the
Python reference on the six checked contexts (roots of (4,5,5), (5,5,6), (4,4,5),
the sibling-inside, one-outer and sandwich contexts).

Four nodes were registered with `es node add` (commit d4139b2):

| node | kind | status 2026-09-06 |
|---|---|---|
| `ctx_card_le_bound` | formalization | proved modulo the two lemma nodes below (module sorry-free) |
| `ctx_satisfies_of_deepBelowSplit` | formalization | open (the union lemma of 0117) |
| `ctx_bound_antitone` | formalization | **proved** (sorry-free, standard axioms) |
| `ctx_bound_additive` | conjecture | falsifier pass (4 cases, 50,268 partitions, 0 violations) |

## The induction step, as proved

`ctx_card_le_bound`: induction on `IsDecomposableOn`.  A singleton gives
`1 ≤ bound` because a single vertex is a cup and a cap, so both limits at its
position are positive and the base value is at least one
(`one_le_decomposableThreshold`).  For a split `S = lower ∪ upper`, with
`mL = cupmax(lower)` and `mU = capmax(upper)`:

1. `ctx_satisfies_of_deepBelowSplit` transfers the context to both parts, with
   sibling maxima `mU` (for `lower`) and `mL` (for `upper`).
2. **Strengthening.** The level-one maximum enters the limits only through the
   level-one join term, whose left and right extensions are empty
   (`leftExt_one`, `rightExt_one`), so it constrains a lower part exactly by
   "own cups ≤ k−1−m".  Since every cup of `lower` has size ≤ `mL`, the lower
   part also satisfies its context with the *larger* maximum `k−1−mL`
   (`satisfies_part_lower_of_cup_le`).  Cup ∪ cap across a deep-below split is
   strong, so `mL + mU ≤ k−1` (`chainMax_add_chainMax_le`); with both parts
   nonempty this puts `k−1−mL` and `mL` in `1..k−2`, and `WellFormed.part`
   passes well-formedness down.
3. The hypotheses give `|lower| ≤ bound(σ_L(k−1−mL))` and
   `|upper| ≤ bound(σ_U(mL))`; `ctx_bound_additive` with `d = k−1−mL` (so
   `k−1−d = mL`) bounds the sum by `bound σ`, after `positionsOf_compl`
   identifies the complement of the lower positions with the upper positions.

**Consequence.** The monotonicity lemma `ctx_bound_antitone` is not needed by the
induction: the two-parameter coupling `(mU, mL)` is replaced by the one-parameter
coupling `(k−1−mL, mL)` through the strengthening, not through domination.  It
stays proved (and is the cleanest statement of why `F2` is monotone in the maxima).

## Helper lemmas in `ESBlueprint/B/CtxCardLeBound.lean`

chain maxima (`chainMax_le_iff`, `le_chainMax_of_isCupSet/CapSet`,
`one_le_chainMax`, `chainMax_add_chainMax_le`); the singleton base
(`numRuns_le_length`, `one_le_baseOf`, `one_le_bound_of_satisfies_singleton`);
letters and sides of a part (`part_letterAt_of_child/ext`,
`part_extPositions_succ`, `part_sideAt_succ`, `part_sideAt_one_of_mem`,
`WellFormed.part`); the level-one maximum (`*_withMaximum`, `levelsOn_one`,
`joinExt_withMaximum_one_le`, `joinExt_withMaximum_one_of_sideAt_ne`,
`satisfies_withMaximum_one_of_cup_le`, `part_eq_withMaximum_one`); positions
(`rank_lt_card`, `rank_lt_rank`, `pos_injOn`, `mem_positionsOf`,
`positionsOf_subset/ne_nil/length_lt/compl`).

`ESBlueprint/B/CtxBoundAntitone.lean` proves `decomposableThreshold` monotone in
each of its first two parameters from 2 on (`decomposableThreshold_mono`, via
`choose_le_sum_choose_window` at the choose/window crossing), `baseOf_mono`, and
the `Dominates` relation on contexts (same word, pointwise larger maxima) under
which every limit is antitone and which `part` preserves.

## What remains for Workstream B

- `ctx_satisfies_of_deepBelowSplit`: the union lemma.  The core already has the
  geometric facts (`HasDeepBelowSplit.insert_upper_isCupSet_iff_isSweepEndpoint`,
  `isStrongPolygonSet_iff_inter_cup_cap`, `cup_union_cap_isStrongPolygonSet`); what
  is left is the bookkeeping from positions in the parent word to `leftExt` /
  `rightExt` / `joinExt` of the part context.
- `ctx_bound_additive`: the open lemma (exchange argument of 0121).
- `decomposableStateUpper_all` from `ctx_card_le_bound` at `Context.root`.

## Harness notes

The full extractor is refused while experiments hold memory; `es node add`,
`es check` and `es falsify` now fall back to a targeted extract over the node's
import closure (commits 2b0ca74, 3394109), so `harness/nodes.json` and
`status.md` lag until the next full `es extract`.
