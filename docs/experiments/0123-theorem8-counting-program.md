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
