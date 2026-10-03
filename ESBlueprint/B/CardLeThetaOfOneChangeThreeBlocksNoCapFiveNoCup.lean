import ESBlueprint.B.CardLeChooseOfOneChangeNoCapFourNoCup
import ESBlueprint.B.ExistsCapStartPeelOfOneChangeNoCapSuccNoCup

namespace ErdosSzekeres

/-- The audited Theta three-block bound and its first-block cup variant under the one-change law, obtained by two localizations of four-cap first points; all three blocks are four-cap-free and the union five-cap-free.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_six_pred_pred_of_seven_le -/
theorem card_le_theta_of_oneChange_three_blocks_no_capFive_no_cup {n v : ℕ} {χ : TripleColoring n} {X Y Z : Finset (Fin n)} (hv : 3 ≤ v)
(hone : OneChangeOn χ (X ∪ Y ∪ Z))
(hXY : ∀ x ∈ X, ∀ y ∈ Y, x < y)
(hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y < z)
(hXZ : ∀ x ∈ X, ∀ z ∈ Z, x < z)
(hXcap : ¬ContainsCapSet χ X 4) (hYcap : ¬ContainsCapSet χ Y 4)
(hZcap : ¬ContainsCapSet χ Z 4)
(hnoCap : ¬ContainsCapSet χ (X ∪ Y ∪ Z) 5)
(hnoCup : ¬ContainsCupSet χ (X ∪ Y ∪ Z) v) :
(X ∪ Y ∪ Z).card ≤ Nat.choose v 2 + Nat.choose (v - 1) 2 + Nat.choose (v - 2) 2 ∧
(IsCupSet χ X → (X ∪ Y ∪ Z).card ≤ Nat.choose v 2 + Nat.choose (v - 1) 2 + (v - 3)) := by
  classical
  let S := X ∪ Y ∪ Z
  have hXS : X ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hYS : Y ⊆ S := Finset.subset_union_right.trans Finset.subset_union_left
  have hZS : Z ⊆ S := Finset.subset_union_right
  obtain ⟨A, hAS, hAmem, hrestCap, hAcup⟩ :=
    exists_capStartPeel_of_oneChange_no_capSucc_no_cup (c := 4)
      (by decide) (by omega : 2 ≤ v) hone hnoCap hnoCup
  have hAxy : A ⊆ X ∪ Y := by
    intro a ha
    obtain ⟨haS, C, hCs, hCcard, hCcap, haC, hCmin⟩ := (hAmem a).mp ha
    by_contra h
    have haZ : a ∈ Z := (Finset.mem_union.mp haS).resolve_left h
    apply hZcap
    refine ⟨C, ?_, hCcard, hCcap⟩
    intro x hx
    have hxS := hCs hx
    rcases Finset.mem_union.mp hxS with hxXY | hxZ
    · rcases Finset.mem_union.mp hxXY with hxX | hxY
      · have := hXZ x hxX a haZ
        have := hCmin x hx
        omega
      · have := hYZ x hxY a haZ
        have := hCmin x hx
        omega
    · exact hxZ
  have hAcap : ¬ContainsCapSet χ A 5 :=
    fun h ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono h hAS)
  obtain ⟨B, hBA, hBmem, hmidCap, hBcup⟩ :=
    exists_capStartPeel_of_oneChange_no_capSucc_no_cup (c := 4)
      (by decide) (by omega : 2 ≤ v - 1) (hone.mono hAS) hAcap hAcup
  have hBX : B ⊆ X := by
    intro b hb
    obtain ⟨hbA, C, hCA, hCcard, hCcap, hbC, hCmin⟩ := (hBmem b).mp hb
    by_contra h
    have hbY : b ∈ Y := (Finset.mem_union.mp (hAxy hbA)).resolve_left h
    apply hYcap
    refine ⟨C, ?_, hCcard, hCcap⟩
    intro x hx
    rcases Finset.mem_union.mp (hAxy (hCA hx)) with hxX | hxY
    · have := hXY x hxX b hbY
      have := hCmin x hx
      omega
    · exact hxY
  have hrestS : S \ A ⊆ S := Finset.sdiff_subset
  have hrestCup : ¬ContainsCupSet χ (S \ A) v :=
    fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hrestS)
  have hrestBound := card_le_choose_of_oneChange_no_capFour_no_cup
    (hone.mono hrestS) hrestCap hrestCup
  have hmidA : A \ B ⊆ A := Finset.sdiff_subset
  have hmidCup : ¬ContainsCupSet χ (A \ B) (v - 1) :=
    fun h ↦ hAcup (FinsetPolygon.ContainsCupSet.mono h hmidA)
  have hmidBound := card_le_choose_of_oneChange_no_capFour_no_cup
    (hone.mono (hmidA.trans hAS)) hmidCap hmidCup
  have hBcap : ¬ContainsCapSet χ B 4 :=
    fun h ↦ hXcap (FinsetPolygon.ContainsCapSet.mono h hBX)
  have hBcup' : ¬ContainsCupSet χ B (v - 2) := by
    simpa only [show v - 1 - 1 = v - 2 by omega] using hBcup
  have hBbound := card_le_choose_of_oneChange_no_capFour_no_cup
    (hone.mono (hBA.trans hAS)) hBcap hBcup'
  have hcard₁ : (S \ A).card + A.card = S.card :=
    Finset.card_sdiff_add_card_eq_card hAS
  have hcard₂ := Finset.card_sdiff_add_card_eq_card hBA
  constructor
  · change S.card ≤ _
    omega
  · intro hXcup
    have hBcupSet : IsCupSet χ B := FinsetPolygon.IsCupSet.mono hXcup hBX
    have hBsmall : B.card < v - 2 := by
      by_contra h
      obtain ⟨D, hDB, hDcard⟩ := Finset.exists_subset_card_eq (by omega : v - 2 ≤ B.card)
      exact hBcup' ⟨D, hDB, hDcard, FinsetPolygon.IsCupSet.mono hBcupSet hDB⟩
    change S.card ≤ _
    omega


end ErdosSzekeres
