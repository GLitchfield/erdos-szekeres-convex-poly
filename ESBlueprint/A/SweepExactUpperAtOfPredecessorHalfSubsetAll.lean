import ErdosSzekeres.StrongPredecessorBicoloring

namespace ErdosSzekeres

/-- Predecessor-half subsets at every level from 4 to k give the sweep-model exact upper bound at k. Route: Nat.le_induction from sweepExactUpperAt_three and sweepExactUpperAt_of_predecessorHalfSubset.
@node
@ws A
@kind formalization
@depends ErdosSzekeres.sweepExactUpperAt_three, ErdosSzekeres.sweepExactUpperAt_of_predecessorHalfSubset
@consumer ErdosSzekeres.forcesConvexPolygon_of_sweepExactUpperAt -/
theorem sweepExactUpperAt_of_predecessorHalfSubset_all (k : ℕ) (hk : 3 ≤ k) (h : ∀ j, 4 ≤ j → j ≤ k → PredecessorHalfSubsetAt j) : SweepExactUpperAt k := by
  sorry

end ErdosSzekeres
