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
| `ctx_satisfies_of_deepBelowSplit` | formalization | **proved** (sorry-free, standard axioms; the union lemma of 0117) |
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

## The context transfer, as proved (same day)

`ESBlueprint/B/CtxSatisfiesOfDeepBelowSplit.lean`.  The part's left and right
extension folds are named (`leftStep`, `rightStep`); a part's own-side levels are
`1 :: (parent levels).map (+1)` (`part_levelsOn_self_*`), its other-side levels are
the shifted parent levels (`part_levelsOn_other_*`), and the level-one letters are
the child positions not kept (`part_extPositions_one`).  Hence every fold of the
part over a sublist of its own-side levels either equals a parent fold from the
same start or, after one step through level one, `1 +` a parent fold from the
position `x` of a sibling vertex outside the chain (`foldl_leftStep_part_le`,
`foldl_rightStep_part_le`); on the other side the extensions are equal
(`chainExt_part_other`, `joinExt_part_other`).

Positions: a part's child positions are exactly the kept positions
(`part_childPositions`, `childPositions_filter_positionsOf`), and the position of a
vertex computed inside the part is its position in the parent (`pos_part_eq`, via
`getElem?_length_filter_lt`: in a strictly increasing list an element sits at the
index counting the smaller ones).

Geometry (from the crossing rule alone): a cup of the lower part stays a cup after
adding upper vertices outside it in sweep order, at most one per side
(`isCupSet_union_of_extremes`), dually for caps of the upper part; the longest
chain is attained (`exists_card_eq_chainMax`).

The generic core `card_add_ext_part_le` then bounds, for any part (either side,
any interleaving), a chain's size plus the part's chain/join extension by the
parent's chain/join limit: each pair of fold values is realized by the chain
extended with the corresponding sibling vertices (`core`), the parent's constraint
on that chain gives the bound, and `add_max_add_max_le` lifts pairwise bounds to
the two maxima.  The level-one join term is `cupmax + capmax ≤ k−1` (cup ∪ cap
strong).  The two `Satisfies` conclusions instantiate it with `P = IsCupSet`,
`param = u` (lower) and `P = IsCapSet`, `param = a` (upper).

## Additivity, decomposed (evening)

`ctx_bound_additive` is now derived (`ESBlueprint/B/CtxBoundAdditive.lean`) from
two conjecture nodes with the same falsifier, split on the number of runs:

| node | content |
|---|---|
| `ctx_bound_cut_le` | **proved**: with at least two runs, every interval cut with every coupling is one of the terms of the recursion's maximum, and the recursion is monotone in its fuel (`boundFuel_le_succ`), so the parts, which have fewer child letters, are evaluated with enough fuel. |
| `ctx_bound_additive_single_run` | conjecture: a single-run context has `bound = base` (the threshold with the run's internal limits); every partition of the run and every coupling gives part bounds summing to at most it.  This is the Baek–Balko one-level inequality carried along with the full positional context. |
| `ctx_bound_additive_multi_run` | conjecture: with at least two runs, an interleaved (non-interval) partition is dominated by the maximum over interval cuts, the exchange argument of 0121. |

So the induction's only remaining gaps are these two, both verified by the
additivity tests (0121, 0122) and by the falsifier.

## What remains for Workstream B

- `ctx_bound_additive_single_run` and `ctx_bound_additive_multi_run` (above).
  With them, `ctx_card_le_bound` is unconditional.
- `decomposableStateUpper_all` from `ctx_card_le_bound` at `Context.root`.
- Shared helper lemmas now live in the core module
  `ErdosSzekeres/DecomposableContextLemmas.lean` (the core cannot import
  ESBlueprint, and several nodes use them).

## Harness notes

The full extractor is refused while experiments hold memory; `es node add`,
`es check` and `es falsify` now fall back to a targeted extract over the node's
import closure (commits 2b0ca74, 3394109), so `harness/nodes.json` and
`status.md` lag until the next full `es extract`.
