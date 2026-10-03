import ErdosSzekeres.StructuralChargingPascalCupBlocks
import ESBlueprint.B.DecomposableThresholdFivePredOfSixLe
import ESBlueprint.B.CardLeTwoChooseAddOneOfDecomposableGapDeepSplitNoCapFiveNoStrongOfInputs

namespace ErdosSzekeres

/-- The diagonal five singleton lower Pascal-tail gate for k at least six, following the audited root split argument and taking the uniform R20 cupblock theorem and exact R21 Baek cardinality bound as explicit hypotheses.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs (hblocks : ∀ k, 5 ≤ k → DiagonalCupBlocksForce4kk k) (hbaek : ∀ {n k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}, 3 ≤ k → OneChangeOn χ s → ¬ContainsCapSet χ s 4 → ¬ContainsStrongPolygonSet χ s k → s.card ≤ 1 + Nat.choose (k - 1) 2) {k : ℕ} (hk : 6 ≤ k) : SingletonLowerPascalTailGate 5 k k := by
  classical
  have hTwo : ∀ {n : ℕ} {χ : TripleColoring n} {P Q : Finset (Fin n)},
      (∀ x ∈ P, ∀ y ∈ Q, x < y) → IsCupSet χ P → IsCupSet χ Q →
      OneChangeOn χ (P ∪ Q) → ¬ContainsCapSet χ (P ∪ Q) 4 →
      ¬ContainsStrongPolygonSet χ (P ∪ Q) k → P.card + Q.card ≤ 2 * k - 4 := by
    intro n χ P Q horder hPcup hQcup hone hn4 hnStrong
    have hdis : Disjoint P Q := Finset.disjoint_left.mpr
      (fun z hzP hzQ ↦ (lt_irrefl z) (horder z hzP z hzQ))
    exact diagonal_cup_block_card_add_le (by omega) (hblocks k (by omega))
      hdis horder hPcup hQcup hone hn4
      (fun h ↦ hnStrong (FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet h)) hnStrong
  have hBaek : ∀ {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)},
      OneChangeOn χ s → ¬ContainsCapSet χ s 4 → ¬ContainsStrongPolygonSet χ s k →
      s.card ≤ 1 + Nat.choose (k - 1) 2 := by
    intro n χ s hone hn4 hnStrong
    exact hbaek (by omega) hone hn4 hnStrong
  intro n χ q upper hupper hdeep hcard hnoCap hnoCup hnoStrong
  have hstep : decomposableThreshold 5 k k = decomposableThreshold 5 (k - 1) k + 1 := by
    rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega),
      decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
    unfold decomposableBinomialWindow
    rw [show k - 1 - 2 = k - 3 by omega]
    have htop : k - 2 = k - 3 + 1 := by omega
    rw [htop, Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.choose_self]
  have hreservoir : lowerPascalTailReservoir 5 k k =
      Nat.choose (k - 1) 2 + Nat.choose (k - 3) 2 + 2 := by
    unfold lowerPascalTailReservoir
    rw [hstep, decomposableThreshold_five_pred_of_six_le hk]
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
  have hcup : ¬ContainsCupSet χ upper k :=
    fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hupperSub)
  have hstrong : ¬ContainsStrongPolygonSet χ upper k :=
    fun h ↦ hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono h hupperSub)
  obtain ⟨A, B, _, _, hAD, hBD, hroot, hsplit⟩ := hupper.exists_split hupperTwo
  have hbound : upper.card ≤ Nat.choose (k - 1) 2 + Nat.choose (k - 3) 2 + 1 := by
    rw [hsplit]
    apply card_le_two_choose_add_one_of_decomposable_gap_deepSplit_no_capFive_no_strong_of_inputs
      hk hTwo hBaek hAD hBD hroot
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
