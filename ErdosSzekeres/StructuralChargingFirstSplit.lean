module

public import ErdosSzekeres.StructuralChargingSingletonRoot

@[expose] public section

/-!
# Separating splits in a decomposition tree

This file isolates the recursive descent that locates a decomposition-tree
split across which a witness set spreads.
-/

namespace ErdosSzekeres

/-- A witness set with at least two vertices inside a decomposable set is
separated by some recursive split contained in the original set. -/
theorem IsDecomposableOn.exists_separating_split
    {n : ℕ} {χ : TripleColoring n} {s witness : Finset (Fin n)}
    (hdecomp : IsDecomposableOn χ s) (hwitnessSub : witness ⊆ s)
    (hwitnessCard : 2 ≤ witness.card) :
    ∃ lower upper : Finset (Fin n),
      IsDecomposableOn χ lower ∧ IsDecomposableOn χ upper ∧
      HasDeepBelowSplit χ lower upper ∧ lower ∪ upper ⊆ s ∧
      witness ⊆ lower ∪ upper ∧
      ¬witness ⊆ lower ∧ ¬witness ⊆ upper := by
  induction hdecomp generalizing witness with
  | singleton i =>
      have hwitnessCardLe : witness.card ≤ 1 := by
        calc
          witness.card ≤ ({i} : Finset (Fin n)).card :=
            Finset.card_le_card hwitnessSub
          _ = 1 := Finset.card_singleton i
      omega
  | @split lower upper hlower hupper hdeep ihlower ihupper =>
      by_cases hwitnessLower : witness ⊆ lower
      · obtain ⟨lower', upper', hlower', hupper', hdeep', hnodeSub,
            hwitnessSub', hwitnessLower', hwitnessUpper'⟩ :=
          ihlower hwitnessLower hwitnessCard
        exact ⟨lower', upper', hlower', hupper', hdeep',
          hnodeSub.trans Finset.subset_union_left, hwitnessSub',
          hwitnessLower', hwitnessUpper'⟩
      by_cases hwitnessUpper : witness ⊆ upper
      · obtain ⟨lower', upper', hlower', hupper', hdeep', hnodeSub,
            hwitnessSub', hwitnessLower', hwitnessUpper'⟩ :=
          ihupper hwitnessUpper hwitnessCard
        exact ⟨lower', upper', hlower', hupper', hdeep',
          hnodeSub.trans Finset.subset_union_right, hwitnessSub',
          hwitnessLower', hwitnessUpper'⟩
      · exact ⟨lower, upper, hlower, hupper, hdeep, Finset.Subset.rfl, hwitnessSub,
          hwitnessLower, hwitnessUpper⟩

end ErdosSzekeres

end
