import ErdosSzekeres.DecompositionPrimeNormalization

namespace ErdosSzekeres

/-- A sweep-model exact upper bound at k transfers to the planar statement: every general-position set of 2^(k-2)+1 points contains a convex k-gon. Route: exists_sweptPresentation, apply h to P.configuration.tripleColoring, then SweptPresentation.containsConvexSubset_iff_exists_isStrongPolygonOn.
@node
@ws A
@kind formalization
@consumer ErdosSzekeres.ErdosSzekeresConjecture -/
theorem forcesConvexPolygon_of_sweepExactUpperAt (k : ℕ) (hk : 3 ≤ k) (h : SweepExactUpperAt k) : ForcesConvexPolygon k (2 ^ (k - 2) + 1) := by
  sorry

end ErdosSzekeres
