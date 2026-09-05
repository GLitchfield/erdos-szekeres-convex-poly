# Experiment 0117: what a subtree at any depth sees, exactly

Date: 2026-09-05 / 06

Status: exact computation on the abstract decomposable class, every claim
verified by brute force on every subtree of every decomposition tree
through eight vertices; no Lean theorem
is claimed.  Workstream B, step 2 of
`docs/plans/workstream-b-self-reliant-plan.md`, second level; continues
experiment 0116.

## Question

Experiment 0116 described what a child of a single deep-below split sees of
its sibling.  An induction on the decomposition tree needs the same for a
subtree at any depth, where external vertices lie both above and below it
at several levels.  What constraints does the avoidance of an `a`-cap, a
`u`-cup and a strong `k`-set by the whole coloring `T` impose on a subtree
`S`, and can they be read off a bounded description of `S`'s context?

## Definitions

`T` is a decomposable coloring, `S` a node of one of its decomposition
trees (reached from the root by deep-below splits with both parts
decomposable).  Along the path from `S` to the root, level `i` has a *side*
(whether the child containing `S` is the lower or the upper part of that
split) and a *sibling* (the other part).  For a cup, cap or strong set
`Q ⊆ S` with at least three vertices, the exact external extension numbers
are

    ext_cup(Q)    = max |X| with X outside S and Q ∪ X a cup of T,
    ext_cap(Q)    = max |X| with X outside S and Q ∪ X a cap of T,
    ext_strong(Q) = max |X| with X outside S and Q ∪ X a strong set of T,

and the constraints on `S` are exactly `|Q| + ext(Q) ≤ a−1, u−1, k−1`.
They were computed by brute force over all subsets of `T`
(`scripts/decomposable_context_functions.py`).

## The rules, and their verification

**Chains stack one vertex per side per level.**  A cup `Q` of `S` grows by
one vertex on the left at every ancestor level where `S`'s side is lower,
taken from that level's (upper) sibling and lying strictly left of the
current left end; the same on the right; levels may be skipped.  So
`ext_cup(Q)` is the length of a longest chain of such levels with
positions decreasing outward on the left, plus the same on the right (a
small dynamic programme over the path), and depends on `Q` only through
its first and last vertex.  Caps are the mirror image (levels where `S` is
upper, siblings below).

**Strong sets join a sibling's chain at exactly one level.**  A strong set
of `T` meeting `S` in a cup `Q` is `Q`, extended as a cup through the
levels below some level `N` where `S` is lower, joined with a cap of the
upper sibling at `N` (any positions); or the pure cup extension.  Hence
`ext_strong(Q) = max( ext_cup(Q), max_N [ ext_cup_{<N}(Q) + capmax(sibling_N) ] )`.
Strong sets of `S` that are neither cups nor caps of `S` extend by nothing.
Caps mirror.

The two first-guess rules were wrong in instructive ways: the one-gap-pair
rule of experiment 0116 (at most one vertex per side in total) failed on
94 of 3,808 subtrees at `n = 6`, all with two above-siblings on the same
side at different levels; and a greedy per-level choice (closest vertex
first) failed on 46 of 67,200 subtrees at `n = 7`, where the first level's
vertex blocks two later levels that together give more.  The longest-chain
form has no exception:

| n | decomposable colorings (all splits) | subtrees examined | exceptions to any of the four rules |
|---|---|---|---|
| 5 | 72 | 248 | 0 |
| 6 | 790 | 3,808 | 0 |
| 7 | 11,386 | 67,200 | 0 |
| 8 | 198,274 | 1,367,052 | 0 |

(The coloring counts exceed the class sizes of experiment 0114 because a
coloring is visited once per decomposition path here.)

## What this settles

The induction state for Theorem 8 is now explicit and exact: a subtree's
context is its list of ancestor levels, each carrying its side, the sweep
positions of that level's sibling relative to the subtree, and the
sibling's longest cap (if the sibling is above) or cup (if below).  From
that list the four constraint functions on `S` are computed by the rules
above, and the constraints on `S` are `|Q| + ext(Q) ≤ a−1, u−1, k−1` for
every cup, cap and strong `Q ⊆ S`.  Nothing else about `T` reaches `S`.
The "external endpoint effect" of the plan is the chain rule, and the
"stacking across tree levels" is the longest chain over levels.

Consequences for the published induction: a scalar child state `(a', u')`
is the special case where every sibling lies entirely on one side of the
child; the `(4,5,5,1,3)` boundary is an interleaved case where the child's
cups are extended on one side only for some positions, so its size is the
positional table of experiment 0116, not a threshold value.

## What is not settled

The extremal function `E(context) = max |S|` over decomposable `S`
satisfying the context's constraints, and a closed form for it, are the
next computation: the state space is finite for each depth, the contexts
that occur through `n = 8` can be enumerated, and the candidate closed forms
are window sums of Pascal rows indexed by the per-side extension profiles.
A closed form `B` with `B(ctx(L)) + B(ctx(U)) ≤ B(ctx(S))` for every split
and interleaving is the paper proof of step 3.

## Reproduction

```console
python3 scripts/decomposable_context_functions.py --max-n 7 --output data/derived/decomposable-context-rules-n7.json
python3 scripts/decomposable_context_functions.py --max-n 8 --output data/derived/decomposable-context-rules-n8.json
```

11 s single core through `n = 7`, 392 s through `n = 8` (under a 12 GiB
cap).  Inputs: the class enumerator of experiment 0114.
