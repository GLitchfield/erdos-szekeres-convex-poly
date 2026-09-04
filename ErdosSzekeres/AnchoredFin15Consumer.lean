module

public import ErdosSzekeres.AnchoredPresentation
public import ErdosSzekeres.StrongPredecessorBaseSix

@[expose] public section

/-!
# The anchored Fin15 endpoint as the fifteen/sixteen middle producer

The fixed-six predecessor-half theorem needs, at ambient cardinalities
fifteen and sixteen, a strong-five-free eight-point support inside every
strong-six-free realizable coloring.  Anchoring (`AnchoredPresentation.lean`)
reduces this to colorings whose vertex `0` sees every later pair as a right
turn, which is the symmetry-broken Fin15 SAT instance.
-/

namespace ErdosSzekeres

/-- The anchored Fin15 endpoint supplies the fifteen/sixteen middle producer
of the fixed-six predecessor-half theorem. -/
theorem predecessorHalfSubsetAtSixMiddle_of_anchoredFin15Endpoint
    (hfin15 : ∀ chi : TripleColoring 15,
      OneChangeOn chi Finset.univ → chi.IsAnchored →
      ¬ContainsStrongPolygonSet chi Finset.univ 6 →
      ∃ support : Finset (Fin 15),
        support.card = 8 ∧ ¬ContainsStrongPolygonSet chi support 5) :
    PredecessorHalfSubsetAtSixMiddle := by
  intro n chi hrealizable hnoStrong hnLower hnUpper
  classical
  obtain ⟨P, rfl⟩ := hrealizable
  let f : Fin 15 ↪o Fin n := Fin.castLEOrderEmb hnLower
  let P' : SweptConfiguration (14 + 1) := P.restrict f
  let A := Classical.choice P'.exists_anchoredReindexing
  let C := A.configuration
  have hone : OneChangeOn C.tripleColoring Finset.univ :=
    C.tripleColoring_isSweepRealizable.oneChangeOn_univ
  have hnoStrongC : ¬ContainsStrongPolygonSet C.tripleColoring Finset.univ 6 := by
    intro h
    have hP' := (A.containsStrongPolygonSet_univ_iff 6).mpr h
    have hrestrict : P'.tripleColoring = P.tripleColoring.restrict f :=
      P.restrict_tripleColoring f
    rw [hrestrict] at hP'
    have := (containsStrongPolygonSet_image_restrict_iff P.tripleColoring f Finset.univ).mp hP'
    exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono this (Finset.subset_univ _))
  obtain ⟨support, hcard, hfree⟩ :=
    hfin15 C.tripleColoring hone A.anchored.tripleColoring hnoStrongC
  let support' : Finset (Fin 15) := support.map A.reindex.symm.toEmbedding
  have hmap : support'.map A.reindex.toEmbedding = support := by
    ext i
    simp [support']
  have hfree' : ¬ContainsStrongPolygonSet P'.tripleColoring support' 5 := by
    intro h
    have := (A.containsStrongPolygonSet_iff support' 5).mp h
    rw [hmap] at this
    exact hfree this
  refine ⟨support'.image f, ?_, ?_⟩
  · intro h
    apply hfree'
    have hrestrict : P'.tripleColoring = P.tripleColoring.restrict f :=
      P.restrict_tripleColoring f
    rw [hrestrict]
    exact (containsStrongPolygonSet_image_restrict_iff P.tripleColoring f support').mpr h
  · rw [Finset.card_image_of_injective _ f.injective, Finset.card_map, hcard]
    omega

end ErdosSzekeres

end
