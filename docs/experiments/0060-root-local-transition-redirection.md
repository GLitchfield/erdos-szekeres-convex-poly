# Experiment 0060: root-local transition redirection

## Question

Does the outer E3 induction really need a tree-global payment and nonreuse
theorem, or can its remaining obstruction be isolated at one decomposable root
split?

Two bounded route reviews were used before changing the main route. The first
tested the proposed all-node pivot ledger and returned `MODIFY` from both Sol
and Fable: fixed-split pivot injectivity did not justify injectivity across
nested nodes, and no payment-completeness theorem connected the ledger to the
outer cardinal bound. The second reviewed the root-local alternative at
evidence-packet SHA-256
`bf8dfc26718600f2874fb8530fef8e097c3db89f3bd1197cea9882b9579e16cd`.
Fable returned `GO` and Sol returned `MODIFY`, but both prioritized the same
root-local route. The review report has SHA-256
`860bee2f6b0f982fdf18846ad566f832d35869930bb4595cabc9b88cf1be6416`.
These verdicts are advisory evidence, not mathematical results.

## Result

The outer hereditary recursion is exactly reducible to one root-local
transition at every positive threshold.

`DecomposableRootTransitionUpper a u k` says that a deep decomposable split
whose two children already have cardinality at most
`decomposableThreshold a u k` cannot exceed that threshold when its union
contains no target `a`-cap, `u`-cup, or strong `k`-gon. Lean proves both
directions:

- the hereditary state immediately implies this root transition; and
- structural induction lifts the root transition to the hereditary state.

The induction handles a large child recursively and lifts its outcome into the
parent. Only when both children are already bounded does it invoke the current
root transition. It never sums payments from different recursive call frames.

Lean also proves that any counterexample larger than the common child bound
contains restricted nonempty children with exact union cardinality
`bound + 1`. Decomposability and the deep-below relation survive restriction.
This removes the mismatch between the exact saturated dispatcher and an
arbitrarily larger root transition.

## Two falsifiers

First, canonical entering-pivot value is not an untagged global identity. On
five ordered vertices, take root lower support `{1,3}` and root upper support
`{0,2,4}`. The hidden lower gap `(1,3)` has entering pivot `2`. Inside the
root upper support, take lower support `{0,4}` and upper support `{2}`. Its
hidden lower gap `(0,4)` also has entering pivot `2`. Lean proves the support
nesting, both hidden-gap facts, and the pivot equality while the candidate
address labels `[]` and `[true]` differ.

This is deliberately a set-level counterexample. It does not construct a
coloring or an explicit `DecompositionTree` realizing both splits. It therefore
does not refute a future state-decorated tree ledger, but it does refute the
unqualified inference from fixed-split pivot injectivity to arbitrary nested
split data.

Second, simultaneous root-pivot retention yields only

```text
card (HiddenGapSource lower upper color) <= selectedCore.card.
```

The saturated-predecessor dispatcher now returns this numeric bound together
with the selected core and universal pivot membership. Yet Lean verifies that
at `(a,u,k) = (4,8,8)` all of the following scalar facts are consistent:

```text
outer threshold + 1 = 23
selected predecessor core size = 8
10 + 13 = 23
8 <= selected predecessor core size
10, 13 <= outer threshold
```

Thus source count and core capacity alone do not contradict the first exact
boundary configuration.

## Lean evidence

`ErdosSzekeres/StructuralChargingRootTransition.lean` proves:

- the definition of the exact root-local transition;
- extraction of an exact nonempty `bound + 1` decomposable subsplit;
- the fixed-root source-count inequality from universal pivot retention;
- a saturated dispatcher returning both that inequality and retention;
- the `(4,8,8)`, `10+13` scalar-consistency theorem; and
- equivalence between the root transition and the hereditary state at positive
  thresholds.

`ErdosSzekeres/StructuralChargingTreePivotCounterexample.lean` proves the
nested set-support collision described above. An independent frozen-file
review accepted both Lean developments, checked the critical restriction and
induction directions, and found no `sorry`, `admit`, unsafe declaration, or
custom axiom.

## Disposition and next gate

The root-local transition route is promoted. The tree-global token carrier
remains valid compiled infrastructure, but a global payment/nonreuse theorem is
no longer the next required result.

The next theorem-design target is a one-split run-length or excess invariant.
It should use the root merge order, hidden and nonhidden adjacency runs, or an
equivalent statistic to couple:

- the two child cardinalities at exact threshold plus one;
- the saturated selected branch and its strict predecessor state;
- current-root avoidance of the target cap, cup, and strong polygon; and
- the pivots retained in the selected predecessor core.

The required conclusion must rule out the exact root boundary, not merely
reprove source count by core size. Before promotion, a proposed invariant must
be falsified against the `(4,8,8)`, `10+13` scalar control and the existing
small structural witnesses. Tree-global aggregation should be reactivated only
if the local proof necessarily compares charges created at descendant nodes.
