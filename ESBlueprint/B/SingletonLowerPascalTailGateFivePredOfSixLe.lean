import ErdosSzekeres.StructuralChargingPascalTails
import ESBlueprint.B.DecomposableThresholdFivePredOfSixLe
import ESBlueprint.B.CardLeTwoChooseOfOneChangeGapDeepSplitNoCapFiveNoCupNoStrong

namespace ErdosSzekeres

/-- For every k at least six, the audited decomposable two-side five-cap bound closes the lower singleton Pascal-tail gate at (5,k-1,k), using the classic Z bound, marker lemma, and cup-plus-four-cap-free row defect.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem singletonLowerPascalTailGate_five_pred_of_six_le {k : ℕ} (hk : 6 ≤ k) : SingletonLowerPascalTailGate 5 (k - 1) k := by
  classical
  intro n χ q upper hupper hdeep hcard hnoCap hnoCup hnoStrong
  have hreservoir : lowerPascalTailReservoir 5 (k - 1) k =
      Nat.choose (k - 1) 2 + Nat.choose (k - 3) 2 + 1 := by
    unfold lowerPascalTailReservoir
    rw [decomposableThreshold_five_pred_of_six_le hk]
    norm_num only [Nat.reduceSub]
    omega
  rw [hreservoir] at hcard
  have hpositive : 0 < Nat.choose (k - 1) 2 := Nat.choose_pos (by omega)
  have hupperTwo : 2 ≤ upper.card := by omega
  have hqNot : q ∉ upper := by
    intro hq
    exact Finset.disjoint_left.mp hdeep.disjoint (Finset.mem_singleton_self q) hq
  have hsides := gap_sides_avoid_cap_of_no_parent_succ_cap (r := 4)
    hdeep (Finset.mem_singleton_self q) hnoCap
  have hupperSub : upper ⊆ {q} ∪ upper := Finset.subset_union_right
  have hcap : ¬ContainsCapSet χ upper 5 :=
    fun h ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono h hupperSub)
  have hcup : ¬ContainsCupSet χ upper (k - 1) :=
    fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hupperSub)
  have hstrong : ¬ContainsStrongPolygonSet χ upper k :=
    fun h ↦ hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono h hupperSub)
  obtain ⟨A, B, hAne, hBne, _, _, hroot, hsplit⟩ := hupper.exists_split hupperTwo
  have hbound : upper.card ≤ Nat.choose (k - 1) 2 + Nat.choose (k - 3) 2 := by
    rw [hsplit]
    apply card_le_two_choose_of_oneChange_gap_deepSplit_no_capFive_no_cup_no_strong
      hk hAne hBne hroot
    · rw [← hsplit]
      exact hqNot
    · rw [← hsplit]
      exact hupper.turnSequenceAllowed
    · rw [← hsplit]
      exact hsides.1
    · rw [← hsplit]
      exact hsides.2
    · rw [← hsplit]
      exact hcap
    · rw [← hsplit]
      exact hcup
    · rw [← hsplit]
      exact hstrong
  omega

end ErdosSzekeres
