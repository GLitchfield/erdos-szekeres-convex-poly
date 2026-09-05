module

public import ErdosSzekeres.Closed.A.SweepExactUpperAtOfPredecessorHalfSubsetAll
public import ErdosSzekeres.Closed.A.ForcesConvexPolygonOfSweepExactUpperAt
public import ErdosSzekeres.Extremal

@[expose] public section

namespace ErdosSzekeres

/-- The headline reduction: the predecessor-half property at every level j ≥ 4 gives the Erdős–Szekeres conjecture, both halves. Upper half: sweepExactUpperAt_of_predecessorHalfSubset_all then forcesConvexPolygon_of_sweepExactUpperAt; sharpness: classical_lower_sharpness.
@node
@ws A
@kind formalization
@depends ErdosSzekeres.sweepExactUpperAt_of_predecessorHalfSubset_all, ErdosSzekeres.forcesConvexPolygon_of_sweepExactUpperAt, ErdosSzekeres.classical_lower_sharpness
@consumer ErdosSzekeres.ErdosSzekeresConjecture -/
theorem erdosSzekeresConjecture_of_predecessorHalfSubsetAt_all (h : ∀ j, 4 ≤ j → PredecessorHalfSubsetAt j) : ErdosSzekeresConjecture := by
  intro n hn
  show ForcesConvexPolygon n (2 ^ (n - 2) + 1) ∧ HasSharpnessExample n (2 ^ (n - 2) + 1)
  refine ⟨?_, classical_lower_sharpness n hn⟩
  exact forcesConvexPolygon_of_sweepExactUpperAt n hn
    (sweepExactUpperAt_of_predecessorHalfSubset_all n hn fun j hj _ => h j hj)

end ErdosSzekeres

end
