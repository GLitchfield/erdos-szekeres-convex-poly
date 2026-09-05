import ErdosSzekeres.Closed.A.SweepExactUpperAtOfPredecessorHalfSubsetAll

namespace ErdosSzekeres

/-- The headline reduction: the predecessor-half property at every level j ≥ 4 gives the Erdős–Szekeres conjecture, both halves. Upper half: sweepExactUpperAt_of_predecessorHalfSubset_all then forcesConvexPolygon_of_sweepExactUpperAt; sharpness: classical_lower_sharpness.
@node
@ws A
@kind formalization
@depends ErdosSzekeres.sweepExactUpperAt_of_predecessorHalfSubset_all, ErdosSzekeres.forcesConvexPolygon_of_sweepExactUpperAt, ErdosSzekeres.classical_lower_sharpness
@consumer ErdosSzekeres.ErdosSzekeresConjecture -/
theorem erdosSzekeresConjecture_of_predecessorHalfSubsetAt_all (h : ∀ j, 4 ≤ j → PredecessorHalfSubsetAt j) : ErdosSzekeresConjecture := by
  sorry

end ErdosSzekeres
