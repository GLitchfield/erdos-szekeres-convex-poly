# E3 adversarial experiment design

## Exact object being tested

A recursive deep-below coloring has a full binary decomposition tree whose
leaves are sweep indices.  At an internal node, a triple meeting both children
is left exactly when its middle sweep index belongs to the lower child; a
triple contained in one child is evaluated recursively.  This is the finite
tree semantics of `HasDeepBelowSplit` used by the current prototype.

For a fixed `k`, the falsification target is a coloring on more than
`2^(k-2)` leaves that has no `k`-element subset satisfying both strong-polygon
four-index equalities.  The target relevant to the Lean theorem must also be
sweep-realizable.  The rank-three signotope law is a necessary but not
sufficient certificate of straight-line realizability and is therefore
reported separately.

## Known proof obstruction

The journal induction chooses auxiliary values `u'` and `a'`.  At
`(a,u,k,u',a') = (4,5,5,1,3)`, its asserted cardinal contributions evaluate
to

```text
S(4,1,5) + choose(3,0) + S(3,5,5) + choose(3,2) = 8,
S(4,5,5) = 7.
```

The first added binomial term is retained even though the Pascal interval into
which the proof later places it is empty.  This invalidates that induction
step but does not constitute a counterexample to E3.

## Producer plan

1. Enumerate decomposition trees with labeled sweep leaves, canonicalizing by
   the induced triple-color bit vector so duplicate decompositions are merged.
2. For each coloring, compute cup, cap, and strong subset maxima exactly.
3. Shard deterministically by a prefix of the color bit vector or canonical
   split code; write atomic shard summaries and any first counterexample.
4. If exhaustive enumeration stops being feasible, formulate the same finite
   conditions as SAT and retain a replayable assignment or unsatisfiability
   certificate rather than relying on solver status.

## Independent checker

The checker will read only a compact leaf count, tree certificate, and claimed
triple-color vector.  It will reconstruct colors from the tree, compare every
triple bit, enumerate all `k`-subsets, check both strong equalities on every
four-subset, and independently check the signotope law.  A geometric branch
additionally needs rational coordinates and exact determinant signs.

## Outcome branches

- **Certified realizable counterexample:** refute the current E3 statement and
  redirect Layer E immediately.
- **Abstract-only counterexample:** repair `IsDecomposable` or strengthen its
  realizability data before further proof work.
- **No counterexample within exhaustive bound plus stable invariant:** select
  the invariant only after Sol/Fable review and prove its first transition in
  Lean.
- **No counterexample without structural signal:** record a bounded negative
  computation and redesign; do not continue an unbounded search.

## Evidence classification

Until an independent checker and coverage manifest exist, results from
`scripts/decomposable_profile_search.py` are heuristics.  A completed bounded
enumeration is an exact computation only within its declared finite bound.  E3
is complete only with a kernel-checked Lean proof.
