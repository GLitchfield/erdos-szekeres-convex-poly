# Residual preflight for the 2026-09-18 trial

- Worktree: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`
- Agent: `codex:01a0b62c-4ff2-7c20-b4d8-616a192610be`
- Cohort: `sol-12h-20260918`
- Setup usage window: `window-c0c40267ea0e4400`
- Scope: read-only mathematical and library preflight. No Lean statement, proof, probe, or research job was started.

## Reviewed boundary

The final accepted proof boundary is `13bf3cd8`. `verified-results.json` records 32 accepted,
sorry-free results with only `propext`, `Classical.choice`, and `Quot.sound`. The two relevant
terminal results are:

- `ctx_extreme_cut_six_pair_intersection_three_residual_classification`, type hash
  `b609724c42011c14`, commit `12fdc631`;
- `ctx_actual_marker_opposite_rank_interval_endpoint_exclusion`, type hash
  `a5cecb39bcbadb6d`, commit `13bf3cd8`.

`checkpoint.md` is append-only. Its early maximum-two, mixed-support, and two-collision
descriptions are historical stages, all superseded by its final `Open work`, filtered-probe, and
endpoint-exclusion sections. The final obstruction is the actual extreme chosen-kept `k=6` cut
whose companion has canonical low/high ordered-rank-pair intersection of cardinality at least
three. The opposite-kept block orientation and all earlier internal-complement cases are closed.

## Exact residual interface

For

```text
rest := σ.childPositions.filter (· ∉ keep)
A    := σ.part keep s m
B    := σ.part rest t n
```

the classifier uses the following canonical objects in `B`:

```text
capacity q := if s=lower then B.cupLimit q q else B.capLimit q q
color q    := if capacity q ≤ 2 then 0 else 1
support c  := B.childPositions.filter (color · = c)
group c    := B with children outside support c changed to a fresh unindexed external level
global     := if t=lower then B.u else B.a
active c   := active children of group c
interval c q := Icc ((group c).leftExt t 0 q + 1)
                      (global - 1 - (group c).rightExt t 0 q)
pairs c    := union over active q of nondecreasing pairs from interval c q
```

Its hypotheses are: positive external labels; distinct axes `s ≠ t`; ordered source levels
`N<M` on `s` with actual positions `x,y`; chosen and opposite globals at most five; every
chosen-axis external occurrence equal to `x` or `y`; an arbitrary `keep`; a child `p` of `A`;
`m+2=σ.k` and `σ.k=6`; and a child `high` of `B` with chosen-axis point capacity at least three.
The conclusion is

```text
((∀ f g, boundFuel f A + boundFuel g B ≤ 12) ∧ A.bound + B.bound ≤ 12)
  ∨ 3 ≤ card (pairs 0 ∩ pairs 1).
```

The statement has no positivity assumption on `n` and no coupling equation
`m+n=σ.k-1`. Consequently it does **not** expose `n=1` or `B.maximumAt 1=1`.

## Companion constructor and synthetic-marker facts

`Context.part keep side maximum` preserves `a,u,k`, keeps listed source children, changes other
source children to external letters at new level one on `side`, shifts every old external level
by one, and prepends `maximum` to `maxima`. Applied to the companion `B`:

- `p ∈ A.childPositions` gives `p ∈ σ.childPositions` and `p ∈ keep` by
  `part_childPositions`.
- Hence `p ∈ B.extPositions 1` by `part_extPositions_one`; the residual proof establishes this
  as `hpB`.
- Nonemptiness at `p` gives `B.sideAt 1=t` by `part_sideAt_one_of_mem`.
- `B.maximumAt 1=n` exactly, by `part_maximumAt_one`.
- Source levels and markers transport as `N+1,M+1`, with sides and positions unchanged, by
  `part_levels`, `part_sideAt_succ`, and `part_extPositions_succ`; old maxima transport by
  `part_maximumAt_succ`.
- Because the new level has side `t≠s`, `part_levelsOn_other_zero` proves that every chosen-axis
  marker of `B` still comes from the source and is at `x` or `y`.
- `ctx_part_positive_letters` supplies positivity for `B`; `B.a=σ.a`, `B.u=σ.u`, and
  `B.k=σ.k` are definitional.

At the actual recurrence interface, the omitted coupling premise repairs the missing fact:
`m+n=σ.k-1`, `m+2=σ.k`, and `n≥1` imply `n=1`. This derivation already appears in
`ctx_nonmonotone_new_marker_cut_bound_except_six_extreme` as `hnOne`. The next theorem should
either retain those premises or take `n=1` / `B.maximumAt 1=1` explicitly. It should not rely on
the present residual classifier alone to recover the maximum.

## Intended `1+11` closure

From `m+2=σ.k=6`, `m=4`. The synthetic chosen level of `A` therefore satisfies
`A.maximumAt 1=A.k-2`, and `ctx_bound_le_one_of_large_sibling_maximum` gives both
`boundFuel f A≤1` and `A.bound≤1`. Closing the residual requires the companion estimates

```text
∀ g, boundFuel g B ≤ 11
B.bound ≤ 11.
```

They combine with the unit estimate to give every independently fueled sum and the full sum at
most twelve. The current overlap-excess theorem only gives

```text
B bound ≤ choose(global,2) + card (pairs 0 ∩ pairs 1),
```

so at `global≤5` the `card≥3` branch goes in the wrong numerical direction. A closing theorem
must couple the two pruning recursions or strengthen a boundary potential using the actual
level-one marker and its maximum one.

The endpoint theorem supplies the structural split needed for such a charge. For an actual
rank-axis marker `x` at level `N` and every child `q`, exactly one alternative holds:

- `x<q`, and every rank in `Icc (leftExt t 0 q + 1) (global-1-rightExt t 0 q)` is at least two;
- `q<x`, and every such rank `r` satisfies `r+2≤global`.

Its proof uses only child/marker disjointness and the singleton level in the extension fold. It
does not use, or imply anything from, `maximumAt N=1`.

## Existing lemmas that fit the next proof

- `ctx_extreme_cut_six_pair_intersection_three_residual_classification`: actual cut dichotomy and
  exact `A/B/pairs` definitions.
- `ctx_extreme_cut_six_twelve_of_pair_intersection_one`: already packages the unit `A` charge and
  companion eleven-bound in the small-overlap branch.
- `ctx_two_marker_mixed_capacity_pair_overlap_excess_bound`: exact inclusion-exclusion bound;
  useful as a baseline, not a closure for `card≥3`.
- `ctx_binary_capacity_pair_intersection_source_witnesses` and
  `ctx_two_marker_pair_collision_source_separated`: move a canonical group-pair collision back to
  active source children and source-history intervals, retaining low/high capacities and
  separation across the older marker.
- `CtxTwoStraddlingPairCollisionsCommonWitnessIntervals`,
  `ctx_pure_extensions_position_monotone`, and
  `rank_pair_triangle_intersection_card_ge_three_of_two_common_ranks`: the compiled geometry that
  rules out intersection cardinality two.
- `ctx_part_pruning_history_transport`: pruning preserves indexed history, pure extensions,
  point limits, and active support exactly. This is the bridge if endpoint exclusion is proved in
  `B` but the charge is stated using `group c` intervals.
- `ctx_bound_le_sum_run_group_prunings` and its capacity-three variant: available recursion
  decompositions, but summing independently is known to lose the needed shared charge.
- `part_maximumAt_one`, `part_maximumAt_succ`, `part_extPositions_one`,
  `part_extPositions_succ`, `part_sideAt_one_of_mem`, `part_sideAt_succ`, and
  `part_levelsOn_other_zero`: exact companion-construction transports.
- `ctx_nonmonotone_new_marker_cut_bound_except_six_extreme`: an existing checked source for the
  extreme arithmetic `n=1` from coupling.

## Reviewed probe and catalog APIs

The reviewed `probe_two_marker_overlap_reused.py` composes four catalogued APIs:

- `decomposable.context-enumeration`: `contexts(...)`, finite abstract signatures only;
- `decomposable.context-limits`: `limits_from_signature(..., lean=True)`, exploratory cup/cap
  matrices with Lean-style truncated subtraction;
- `research.recursive-bounds`: `evaluator(...,
  semantics="context-bound-zero-children-v1")`, the retained recursive evaluator;
- `research.context-extension`: `extension(word, depth, side, p, left)`, pure extension length.

All four catalog entries explicitly disclaim kernel proof credit/equivalence. The reuse variant
maps each maximal `S` run to its first physical position and replaces only the local extension DP.
Review receipt `extension-reuse-parity-receipt.json` records 14,464 signatures, 59,520 old/new
extension pairs, 119,040 representative-invariance checks, and byte-identical complete output in
guarded job `20260917-204046-b5cf98`.

The audited `s_max=4` result is:

- bare exact-two-marker domain: 1,984 signatures, 128 mixed residuals, 40 values equal to twelve;
  all overlaps were ten. This falsifies the proposed bare `overlap≥3 → bound≤11` direction in the
  retained semantics;
- minimal synthetic-marker domain: 12,480 signatures, 824 mixed residuals, maximum value eleven,
  no violation; overlaps were 304 of size three and 520 of size six. The 52 value-eleven cases
  include pair-set sizes `6+6` with overlap three and `6+9` with overlap six.

The companion generator is materially narrower than the Lean residual. It fixes `(a,u,k)=(5,5,6)`,
at most four children, exactly three indexed levels, exactly one marker occurrence at each level,
`maximumAt 1=1`, and no additional history. It checks shape-compatible contexts, not a theorem
that every generated signature is the image of the actual `part` constructor with the required
source and cut. The residual theorem permits arbitrary child count, arbitrary additional indexed
history (including opposite-axis history and unused levels), multiple occurrences at the synthetic
level, globals below five, and an unconstrained `n`.

## Logical gaps to guard against in the trial

1. The current residual interface forgets the coupling and therefore forgets the synthetic
   marker's maximum one. Add that fact at the statement boundary before attempting the charge.
2. `ctx_actual_marker_opposite_rank_interval_endpoint_exclusion` concerns source intervals in
   `B`; canonical `pairs` are defined with pruned `group c` intervals. Use the exact pruning
   transport/source-witness lemmas rather than rewriting these as definitionally equal.
3. Existing two-marker separation puts low/high witnesses on opposite sides of the older chosen
   marker `y`, not on prescribed sides of the synthetic marker `p`. Endpoint exclusion partitions
   by `p`; an alignment or a casewise shared-charge argument is still missing.
4. Endpoint loss is a pure-extension fact, while maximum one enters `joinExt`/strong capacity.
   Neither fact alone couples the two pruning recursions. The new invariant must use both.
5. Separate pair-cardinality estimates cannot prove eleven: reviewed equality cases have
   `6+6-3=9` and `6+9-6=9` union counts while the recursive value is eleven. The charge must include
   recursive/base contributions, not only pair-set inclusion-exclusion.
6. A full-bound-only lemma is insufficient for the residual theorem's independent-fuel branch
   unless an existing general fuel-to-bound inequality is supplied. Prefer a theorem stating both
   every-fuel and full `B≤11` estimates, as the accepted chain does.
7. The finite evidence does not cover extra history, multiple synthetic markers, or more than four
   children. Any universal theorem needs a symbolic induction/potential argument; extending the
   probe is evidence only and the reviewed five-child output is empty.

The safest first target is therefore a cut-specific (or explicitly level-one-marker/max-one)
companion theorem returning every-fuel and full `B≤11`, with the exact binary capacity groups and
the actual marker retained throughout. A bare two-marker theorem is contradicted by the reviewed
bounded model.
