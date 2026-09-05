import ErdosSzekeres.StrongPredecessorBicoloring

namespace ErdosSzekeres

/-- Predecessor-half subsets at every level from 4 to k give the sweep-model exact upper bound at k. Route: Nat.le_induction from sweepExactUpperAt_three and sweepExactUpperAt_of_predecessorHalfSubset.
@node
@ws A
@kind formalization
@depends ErdosSzekeres.sweepExactUpperAt_three, ErdosSzekeres.sweepExactUpperAt_of_predecessorHalfSubset
@consumer ErdosSzekeres.forcesConvexPolygon_of_sweepExactUpperAt -/
theorem sweepExactUpperAt_of_predecessorHalfSubset_all (k : ℕ) (hk : 3 ≤ k) (h : ∀ j, 4 ≤ j → j ≤ k → PredecessorHalfSubsetAt j) : SweepExactUpperAt k := by
  induction k, hk using Nat.le_induction with
  | base => exact sweepExactUpperAt_three
  | succ m hm ih =>
    have hprev : SweepExactUpperAt (m + 1 - 1) := by
      rw [Nat.add_sub_cancel]
      intro n χ hreal hcard
      exact ih (fun j hj hjm => h j hj (Nat.le_succ_of_le hjm)) hreal hcard
    intro n χ hreal hcard
    exact sweepExactUpperAt_of_predecessorHalfSubset (by omega) hprev
      (h (m + 1) (by omega) le_rfl) hreal hcard

end ErdosSzekeres
