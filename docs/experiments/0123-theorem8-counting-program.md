# 0123 — Towards a proof of Theorem 8: what the formula counts

**Date:** 2026-09-06 (evening).  **Context:** after 0122 the formal chain rests on
two additivity conjectures of the interval-cut recursion `F2`
(`ctx_bound_additive_single_run`, `ctx_bound_additive_multi_run`).  No proof of
Theorem 8 is available to us; this note records what the threshold's shape says
about how a proof must go, one negative experiment, and the program that follows.

## 1. The threshold counts subsets of a `(k−2)`-set

In the window regime `T(a,u,k) = Σ_{j=k−a}^{u−2} C(k−2, j)` is the number of
subsets of `[k−2]` with at least `k−a` and at most `u−2` elements, equivalently
binary strings of length `k−2` with at most `u−2` letters `L` and at most `a−2`
letters `U`.  On the diagonal it is `2^{k−2}`; in the choose regime
`C(a+u−4, a−2)` is the classical cup–cap count.  Two identities hold
(checked numerically to `k = 15`):

* Pascal, for `3 ≤ a, u ≤ k`: `T(a,u,k) = T(a−1,u,k−1) + T(a,u−1,k−1)`
  (at `a = u = 2` the left side is 1 and the right side 0, the one-vertex
  convention).
* Window split: for `a + u ≥ k + 3` and `k−u+1 ≤ d ≤ a−2`,
  `T(a,u,k) = T(a, k−d, k) + T(d+1, u, k)`: the coupling `d` of a deep-below
  split cuts the window `[k−a, u−2]` into `[k−a, k−d−2]` (the lower part,
  whose cups are limited to `k−1−d`) and `[k−d−1, u−2]` (the upper part,
  whose caps are limited to `d`).

The second identity is exactly the one-level additivity of `F2` at a root
context: the lower part's window is the size range below `k−1−d`, the upper
part's above.  The depth-one closed form of 0118 is, in every case, a union of
such windows: the plain case `T(a, 1+min(u−1−b−e, k−1−max(b+e,d)), k)` has
sizes `≤ k−2−d`, and the sibling-inside two-part maximum
`T(a, c+1, k) + T(d'+1, ·, k)` with `c + d' ≤ k−1` is two disjoint windows.  So at
depth one the parts of every cut own disjoint size ranges inside the parent's
window.

## 2. The naive path lemma is false

A decomposable set is a binary tree with the vertices as leaves; the count of
root-to-leaf paths with at most `u−2` lower-steps, at most `a−2` upper-steps and
length at most `k−2` is `T(a,u,k)` (shorter admissible paths extend to length
`k−2`, so the antichain bound is the window sum).  If every decomposition tree
of a coloring with no `u`-cup, `a`-cap, strong `k`-set obeyed those per-path
bounds, Theorem 8 would follow with no additivity.  It does not
(`scripts/decomposable_path_lemma_test.py`, all decomposable colorings to
`n = 7`, all trees, `data/derived/decomposable-path-lemma-n7.json`):

| n | colorings | every tree obeys the bounds | some tree obeys them |
|---|---|---|---|
| 5 | 62 | 0 | 36 |
| 6 | 718 | 4 | 312 |
| 7 | 10,596 | 94 | 3,688 |

The all-right-turn coloring (one `n`-cap) already has trees with a leaf on the
lower side twice while `cupmax = 2`.  Steps of the path are not the letters of
the label: a sibling vertex extends a chain only when it lies outside the
chain's sweep span, and inside it produces the other chain type.

## 3. The labeling program

What the identities suggest instead is an injection of the vertices into the
subsets of `[k−2]` built along the tree, in which each context `σ` owns a label
set `L(σ)` and every split with coupling `d` hands the lower part labels from
`L(σ)` of size `≤ k−2−d` and the upper part labels of size `≥ k−1−d`.  Two
observations fix what `L(σ)` can and cannot be:

* Size alone cannot be the whole label.  If every split separated by size,
  any two leaves would differ in size at their lowest common ancestor, giving
  at most `k−1` leaves.  So within the size classes the splits must separate
  by membership of individual elements, as Pascal's `C(m, j) = C(m−1, j−1) +
  C(m−1, j)` does, and the label sets of deep contexts are not size windows.
  This is the structural reason behind 0121's finding that `F2` is a
  recursion and not a window sum, and it is where the interleaving enters:
  the choose-type splits reduce the ground set, the window-type splits the
  size range.
* The candidate label sets are therefore "cylinder windows"
  `{X ⊆ [k−2] : |X| ∈ W, X ∩ P = Q}` for a size window `W` and a fixed pattern
  `Q` on a set `P` of positions determined by the context's levels, of
  cardinality `Σ_{j ∈ W} C(k−2−|P|, j−|Q|)`.  At `k = 6` every exact
  value in the 12,724-signature table of `(4,5,6)` (values 3 to 8) is such a
  count, but small values are almost always representable, so this is weak
  evidence.

The conjecture to test next, and the statement whose proof would replace both
additivity conjectures: there is a rule `σ ↦ L(σ) ⊆ 2^{[k−2]}` with
`|L(root a u k s)| = T(a,u,k)`, `L(σ) ≠ ∅` whenever a single vertex satisfies
`σ`, and for every deep-below split of a set satisfying `σ` with parts
satisfying `π_L`, `π_U` (contexts as in `ctx_satisfies_of_deepBelowSplit`),
`L(π_L)` and `L(π_U)` disjoint subsets of `L(σ)`.  Then `|S| ≤ |L(σ)|` by
induction on the tree, with distinct labels at the leaves, and Theorem 8 is the
root case; the formal induction of 0122 carries over verbatim with `bound`
replaced by `|L|`.  The test is computational: compute `L` by the recursive
rule on the signature tables and check disjointness and containment for every
partition, as the additivity tests did for counts.

## Reproduction

    python3 scripts/decomposable_path_lemma_test.py --max-n 7 --output data/derived/decomposable-path-lemma-n7.json

## 4. The computations (same evening)

**Rule-based label sets fail at depth one.**  `scripts/decomposable_label_sets.py`
gives every single-run context the cylinder `{#L(free) ≤ cl−1, #U(free) ≤ pl−1}` with
just enough fixed positions for the choose regime (letters from the sides of the
outermost levels) and every multi-run context the union over its partitions; at
`(4,4,5)`, `(4,5,5)` with three child letters the parts' sets are not inside the
parent's (10 and 12 containment failures), because a part entering the choose regime
fixes a letter its window-regime parent never fixed.  The fixed letters depend on the
split history, so no rule reading only the context's limits and levels works.

**Existence, by SAT.**  A consistent system of label sets exists iff the leaf
contexts (one child letter, positive limits) reachable from the root by any chain
of partitions can be colored with `T` colors so that no split has both parts
reaching leaves of the same color (`scripts/decomposable_label_coloring.py`; the
reachability closure encodes the sets).  At `s = T+1` child letters, over every
partition (any interleaving), both orientations and all couplings
(`data/derived/label-sets/color-*.json`):

| case | s | contexts | leaves | `T` colors | `T−1` colors |
|---|---|---|---|---|---|
| (3,3,3), (3,3,4) | 3 | 37, 121 | 16, 64 | SAT | UNSAT |
| (3,4,4), (3,4,5), (3,4,6) | 4 | 1,625 / 5,053 / 11,505 | 606 / 2,355 / 5,956 | SAT | UNSAT |
| (4,4,4), (3,5,5), (3,5,6) | 5 | 25,721 / 96,985 / 305,329 | 8,524 / 32,496 / 124,792 | SAT | UNSAT |
| (4,4,5), (4,5,5), (4,5,6) | 5 (< T+1) | 133,381 / 135,361 / 437,041 | 63,072 / 67,899 / 259,460 | SAT | — |

So the context-level injection exists in every case tried, and `T` is exactly the
number of labels it needs: with `T−1` labels some full partition tree with `T`
live leaves refutes it, which is the tightness of the threshold.  Since the
coloring subsumes the count statement (a tree with `T+1` live leaves would need
`T+1` colors), this also verifies the all-partition recursion `≤ T` at these sizes.

**What the sets must depend on.**  `scripts/decomposable_label_rule_sat.py`
asks for label sets that are a function of a feature vector of the context, with
containment and disjointness at every split and at most `T` labels at the root.
With the whole context as the feature (the bare conjecture, sets consistent across
all occurrences of a context) it is SAT at every `s = T+1` case above.  Coarsening
a single-run context to its limits `(n, cl, pl)`, or to limits plus level sides, or
plus sibling maxima, is UNSAT already at `(3,4,5)`; coarsening to limits plus the
*word* (positions and sides of the external letters, maxima dropped) stays SAT in
every case run.  So the label set of a run is determined by where the external
letters lie, not by the sibling maxima beyond their effect on the limits.


**Feature-rule runs, complete** (`data/derived/label-sets/rule-*.json`; classes = distinct feature vectors):

| case | s | context | word | limits | sides | maxima |
|---|---|---|---|---|---|---|
| 3,3,3 | 3 | SAT (37) | SAT (37) | — | — | — |
| 3,3,4 | 3 | SAT (121) | SAT (43) | — | — | — |
| 3,4,4 | 4 | SAT (1625) | SAT (642) | — | — | — |
| 3,4,5 | 4 | SAT (5053) | SAT (814) | UNSAT (269) | UNSAT (307) | UNSAT (689) |
| 3,4,6 | 4 | SAT (11505) | SAT (992) | — | — | — |
| 3,5,5 | 5 | SAT (96985) | SAT (14832) | — | — | — |
| 3,5,6 | 5 | SAT (305329) | SAT (25183) | — | — | — |
| 4,4,4 | 5 | SAT (25721) | SAT (11371) | — | — | — |
| 4,4,5 | 5 | SAT (133381) | SAT (19777) | — | — | — |
| 4,5,5 | 5 | SAT (135361) | SAT (24617) | — | — | — |

The solver's sets are not canonical (it fills unconstrained contexts freely), so
the rule itself is not read off yet; pinning the root to the canonical window
(`--root-window`) is satisfiable and is the starting point for extracting one.

## Reproduction

    python3 scripts/decomposable_label_coloring.py --case 3,5,6 --s 5            # T colors
    python3 scripts/decomposable_label_coloring.py --case 3,5,6 --s 5 --colors 3
    python3 scripts/decomposable_label_rule_sat.py --case 3,4,5 --s 4 --features word --root-window --output out.json

## 5. The shape of the label sets (2026-09-07, after a second OOM)

All runs below are `scripts/decomposable_label_rule_sat.py` on the four cases
`(3,4,5) s=4`, `(4,4,5) s=5`, `(4,5,5) s=5`, `(5,5,5) s=5`, root pinned to the
canonical window, every run under an 8 GB cgroup (the unconstrained SAT runs of the
previous evening took WSL down); the run index is
`data/derived/label-sets/tight/index.json`.

* **Every single-run label set can be a cylinder window**: fixed letters on some
  positions, `#L(free) ≤ ℓ`, `#U(free) ≤ υ` with `ℓ ≤ cl−1`, `υ ≤ pl−1`.  With the
  sets allowed to be unions of such cylinders this is SAT even when the cylinder may
  depend only on the run limits and per-level (side, left-flag, right-flag); with a
  *single* cylinder per class it needs the word (positions and sides of all external
  letters): SAT with word features, UNSAT with per-level counts.
* **The fixed positions can be a prefix** (SAT everywhere with word features).
* **Sizes.**  Demanding exactly the threshold `T(pl+1, cl+1, k)` labels for every
  single-run context is consistent for `(3,4,5)`, `(4,4,5)`, for `(4,5,5)` up to
  three levels and for `(5,5,5)` only at one level; deeper contexts must sometimes
  own fewer labels than the recursion's base value (the base is an upper bound, not
  a capacity).  Demanding `min(n, T)` instead is inconsistent: a context's set is the
  set of labels its vertices may carry, not a count of vertices.
* **The canonical shape** `f₀ = max(0, (k−2) − (cl−1) − (pl−1))` fixed positions as a
  prefix, budgets exactly `(cl−1, pl−1)`, is SAT with the letters left free (both
  `(3,4,5)` and `(4,4,5)`).  So only the fixed *letters* are unknown.  Eight simple
  rules for them (sides of the levels in inner, outer, nearest-letter or
  farthest-letter order, padded with L or U) are all UNSAT already at `(3,4,5)`;
  the letters depend on the split history in a way none of these orders captures.
  The backbone (which letter tuples are feasible per context, and which are forced)
  is being computed for `(3,4,5)`.

**Reading.**  In the window regime the two parts of a cut are separated by counts
alone: the lower part has `#L ≤ cl_A − 1`, the upper `#U ≤ pl_R − 1`, and these are
disjoint exactly when `cl_A + pl_R ≤ k−1`, the coupling.  A context needs dead
(fixed) positions precisely when `cl + pl ≤ k−1`, i.e. when the strong-set bound is
slack for it, and then a maximal strong set through one of its vertices has fewer
than `k−1` vertices.  This suggests the semantic label: for a vertex `v`, a
canonical maximal strong set through `v`, encoded by which of its other vertices
lie on the cup side (`L`) and which on the cap side (`U`), the count constraints
`#L ≤ u−2`, `#U ≤ a−2` being exactly that a cup has at most `u−1` and a cap at most
`a−1` vertices, with the deficiency to `k−2` filled by letters that record how the
budget was lost.  Distinct vertices in different parts of a split then differ by
the coupling; the letters of the dead positions are what has to make vertices in
the same part differ, and that is the open part of the rule.

## 6. The dead letters: a near-rule and its exceptions (2026-09-07)

With the shape fixed (`f₀` dead letters as a prefix, tight budgets), the backbone of
the `(3,4,5)` instance (`data/derived/label-sets/tight/backbone-3,4,5-s4.json`,
1,775 solves) gives for each of the 313 single-run classes the set of feasible
dead-letter tuples: 226 classes have exactly one, 71 have two, 16 have three.

Reading the forced tuples: every dead letter is a *loss event* of the run's limits
relative to the root, `L` for a unit lost from the cup limit and `U` for a unit lost
from the cap limit, and the letter order follows the geometry of the events.  Where
two events come from two different levels each with a single letter, the event whose
letter lies *farther* from the run comes first, ties going to the outer level.  A
rule built on that (losses attributed level by level from the restricted limits,
levels sorted by nearest-letter distance descending then level descending, each level's
losses with its side letter first) reproduces a feasible tuple for 282 of the 313
classes; the 31 exceptions are all three-letter, single-label contexts
(`cl = pl = 1`) in which the loss letters of one level are *interleaved* with those of
another, e.g. `S2U2U1L` (cup limit 1 through one extension loss and one join loss at
level 1, cap limit 1 through level 2) is forced to `LUL`, not `LLU`.  So the unit of
the rule is the loss *event*, not the level: extension losses carry the position of
their letter, join losses (the sibling maximum) carry none, and their relative order is
what remains to be found.  The eight orders by level alone, the block rule (losses
grouped by level, outer first) and this distance rule are all unsatisfiable as exact
rules on `(3,4,5)`; the free-letter shape is satisfiable, so a rule exists.

The backbone for `(4,4,5)` at five letters is being computed (capped) for the next
round; it contains two-letter classes with window slack, which `(3,4,5)` lacks.

## 7. The (4,4,5) backbone: the local rule search saturates (2026-09-07)

The backbone of the `(4,4,5)` instance at five letters
(`data/derived/label-sets/tight/backbone-4,4,5-s5.json`: 6,407 single-run
classes, 34,071 solves, 4.0 h under a 4 GiB cap) gives 2,871 forced classes,
1,982 with two feasible tuples, 540 with three, 472 with four and 542 with five;
the dead-letter counts are 0 to 3.  Three findings close the local-rule line.

*More losses than dead letters.*  At `(4,4,5)` the root has one unit of slack
(`a + u − 4 = 4` against `k − 2 = 3`), so every class with a loss has exactly one more
loss event than dead letters, e.g. `1L1L2U2US|2|2` lost one cup unit and one cap unit
but has `f₀ = 1`, forced to `U`.  So beyond the order, a rule has to say which loss is
absorbed, and the root window decides part of it: at `(3,4,5)` no label has two `U`,
which is why `S2U2U1L` (two cap units lost) is `LUL` and not `UUL`.

*No function of the loss events.*  Grouping the classes by a feature and
intersecting the feasible sets of each group is a necessary condition for any rule
that is a function of the feature (`scripts/decomposable_label_backbone_analyze.py`,
summary in `data/derived/label-sets/tight/backbone-4,4,5-s5-analysis.json`; the test
is instantaneous).  The limits alone conflict in 4 of 9 groups; the full multiset of
loss events with letter, level, kind, distance, run side and child side conflicts in
106 of 3,107 groups (`S1U2L3U3U|2|1` is `LU`, `S2L1U3U3U|2|1` is `UL`: same events,
the level-1 and level-2 letters exchanged in position); erasing the levels from the
word conflicts in 224 of 353 groups.  Only the word itself is conflict-free.  The
event-ordering search of §6 gives at most 5,451 of 6,407 (85 %), with "outer level
first" the only feature that matters (every refinement ties); purely positional
orders are worse (3,961).

*Why: the letter position is a cut depth, and the order is global.*  In the tight
regime a cut fixes one letter for each part (`L` for the part that lost a cup unit,
`U` for the other), and Pascal's rule is exactly this split.  The levels of a leaf's
word record the cut order (`part` makes the new letters level 1 and shifts the
rest), so "outer level first" is the cut order, and that is why it is right most of
the time.  It is not always right because a multi-run context must contain the
unions of *all* its interval cuts at once, and the SAT reconciles those through
choices that interleave the letters of different levels.  For the inequality
`Σ_leaves T ≤ T(root)` along one cut tree, tree-dependent prefixes suffice; a
*context-determined* label set, which is what `ctx_card_le_bound` consumes as a
bound function, needs the global reconciliation, and no local rule expresses it.

Consequences.  The dead-letter program stops here: the labeling exists (§4), its
shape is known (§5), and its letters are a global, not a local, choice.  What remains
for the two conjectures is the exchange argument of experiment 0121 §1 for interval
cuts, stated for the recursion directly; the label sets were a route to it, not a
shortcut around it.  The one cheap formal step available now is the boundary case of
`ctx_bound_additive_single_run` (the kept part a prefix or suffix of the run, both
parts single-run), which is the Pascal identity plus the window split of §1 once the
part limits are computed.
