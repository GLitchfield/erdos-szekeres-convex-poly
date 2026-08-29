module

public import ErdosSzekeres.SmallCases
public import ErdosSzekeres.StrongPredecessorBicoloring

@[expose] public section

/-!
# The predecessor half-subset endpoint at four

Every sweep-realizable strong-four-free coloring has at most four vertices.
The whole carrier suffices through two vertices; otherwise any two vertices
form a strong-three-free support of at least half the carrier.
-/

namespace ErdosSzekeres

/-- The fixed base case of the predecessor half-subset recurrence. -/
theorem predecessorHalfSubsetAt_four : PredecessorHalfSubsetAt 4 := by
  intro n χ hrealizable hnoStrong
  obtain ⟨P, rfl⟩ := hrealizable
  have hn : n ≤ 4 := by
    by_contra hn
    have hfive : 5 ≤ n := by omega
    obtain ⟨f, hstrong⟩ := P.exists_strong_four_of_five_le hfive
    apply hnoStrong
    refine ⟨Finset.univ.image f, Finset.subset_univ _, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · exact FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong
  have small_is_free (support : Finset (Fin n)) (hsmall : support.card < 3) :
      ¬ContainsStrongPolygonSet P.tripleColoring support (4 - 1) := by
    rintro ⟨polygon, hpolygonSub, hpolygonCard, _⟩
    have hcardLe := Finset.card_le_card hpolygonSub
    norm_num at hpolygonCard
    omega
  by_cases hnSmall : n ≤ 2
  · refine ⟨Finset.univ, ?_, ?_⟩
    · apply small_is_free
      simp
      omega
    · simp
      omega
  · have htwo : 2 ≤ (Finset.univ : Finset (Fin n)).card := by
      simp
      omega
    obtain ⟨support, _hsub, hsupportCard⟩ := Finset.exists_subset_card_eq htwo
    refine ⟨support, small_is_free support ?_, ?_⟩
    · omega
    · omega

end ErdosSzekeres

end
