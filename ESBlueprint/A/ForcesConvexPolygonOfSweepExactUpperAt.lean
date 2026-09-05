import ErdosSzekeres.DecompositionPrimeNormalization

namespace ErdosSzekeres

/-- A sweep-model exact upper bound at k transfers to the planar statement: every general-position set of 2^(k-2)+1 points contains a convex k-gon. Route: exists_sweptPresentation, apply h to P.configuration.tripleColoring, then SweptPresentation.containsConvexSubset_iff_exists_isStrongPolygonOn.
@node
@ws A
@kind formalization
@consumer ErdosSzekeres.ErdosSzekeresConjecture -/
theorem forcesConvexPolygon_of_sweepExactUpperAt (k : ℕ) (hk : 3 ≤ k) (h : SweepExactUpperAt k) : ForcesConvexPolygon k (2 ^ (k - 2) + 1) := by
  intro s hcard hgp
  classical
  let P := Classical.choice (exists_sweptPresentation s hgp)
  have hlt : 2 ^ (k - 2) < s.card := by omega
  obtain ⟨polygon, -, hpolygonCard, hstrong⟩ :=
    h P.configuration.tripleColoring_isSweepRealizable hlt
  rw [P.containsConvexSubset_iff_exists_isStrongPolygonOn k]
  subst hpolygonCard
  exact ⟨polygon.orderEmbOfFin rfl,
    FinsetPolygon.IsStrongPolygonSet.isStrongPolygonOn_orderEmbOfFin hstrong⟩

end ErdosSzekeres
