module

public import ErdosSzekeres.ES5Certificate
public import ErdosSzekeres.HalfPureDeepSplitFin8
public import ErdosSzekeres.StrongPredecessorBicoloring
public import ErdosSzekeres.TripleColoringRealizability

@[expose] public section

/-!
# The fixed predecessor-half base at five

The exact nine-point strong-five theorem bounds a strong-five-free sweep
configuration by eight vertices.  Up through seven vertices, the elementary
predecessor bicoloring supplies a half-sized strong-four-free support.  At
eight vertices, the exact half-pure deep-split theorem supplies such a support
through the inverse stepping-up kernels.
-/

namespace ErdosSzekeres

/-- The fixed `k = 5` case of the predecessor half-subset recurrence. -/
theorem predecessorHalfSubsetAt_five : PredecessorHalfSubsetAt 5 := by
  intro n χ hrealizable hnoStrong
  obtain ⟨P, rfl⟩ := hrealizable
  have hn : n ≤ 8 := by
    by_contra hn
    have hnine : 9 ≤ n := by omega
    obtain ⟨f, hf⟩ := P.exists_strong_five_of_nine_le hnine
    exact hnoStrong ⟨Finset.univ.image f, Finset.subset_univ _,
      by simpa using Finset.card_image_of_injective Finset.univ f.injective,
      FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hf⟩
  by_cases hnSmall : n ≤ 7
  · obtain ⟨red, blue, hdisjoint, hunion, hred, hblue⟩ :=
      exists_strongPredecessorBicoloring_of_card_le_two_mul_sub_three
        (k := 5) (by omega) hnSmall hnoStrong
    have hcard : n = red.card + blue.card := by
      have hunionCard := congrArg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisjoint] at hunionCard
      simpa using hunionCard.symm
    by_cases hle : blue.card ≤ red.card
    · exact ⟨red, hred, by omega⟩
    · exact ⟨blue, hblue, by omega⟩
  · have hnEight : n = 8 := by omega
    subst n
    obtain ⟨lower, upper, hsplit, hlower | hupper⟩ :=
      halfPureDeepSplitAtFiveFinEight_of_oneChange
        P.tripleColoring P.oneChangeOn_univ hnoStrong
    · exact ⟨lower,
        hsplit.predecessorFree_lower_of_cupPure
          (by omega) hlower.1 hnoStrong hlower.2.2,
        hlower.2.1⟩
    · exact ⟨upper,
        hsplit.predecessorFree_upper_of_capPure
          (by omega) hupper.1 hnoStrong hupper.2.2,
        hupper.2.1⟩

end ErdosSzekeres

end
