import ESBlueprint.B.CardLeThetaOfOneChangeThreeBlocksNoCapFiveNoCup
import ESBlueprint.B.ContainsCupSetSuccOrContainsCapSetSuccOfOneChangeCommonEndpoint

namespace ErdosSzekeres

/-- Audited L3 and L3-cup bounds for three ordered four-cap-free blocks, adjacent five-cap-free unions and six-cap-free total. A common-endpoint extension combines the five-cap start family and second four-cap start family into one smaller-cup-free piece.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_six_pred_pred_of_seven_le -/
theorem card_le_choose_add_two_choose_of_oneChange_three_blocks_no_capSix_no_cup {n v : ℕ} {χ : TripleColoring n} {X Y Z : Finset (Fin n)} (hv : 3 ≤ v)
(hone : OneChangeOn χ (X ∪ Y ∪ Z))
(hXY : ∀ x ∈ X, ∀ y ∈ Y, x < y)
(hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y < z)
(hXZ : ∀ x ∈ X, ∀ z ∈ Z, x < z)
(hXcap : ¬ContainsCapSet χ X 4) (hYcap : ¬ContainsCapSet χ Y 4)
(hZcap : ¬ContainsCapSet χ Z 4)
(hXYcap : ¬ContainsCapSet χ (X ∪ Y) 5)
(hYZcap : ¬ContainsCapSet χ (Y ∪ Z) 5)
(hnoCap : ¬ContainsCapSet χ (X ∪ Y ∪ Z) 6)
(hnoCup : ¬ContainsCupSet χ (X ∪ Y ∪ Z) v) :
(X ∪ Y ∪ Z).card ≤ Nat.choose v 2 + 2 * Nat.choose (v - 1) 2 ∧
(IsCupSet χ X → (X ∪ Y ∪ Z).card ≤ Nat.choose v 2 + Nat.choose (v - 1) 2 + (v - 2)) := by
  classical
  let U := X ∪ Y ∪ Z
  have hXU : X ⊆ U := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ U := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ U := Finset.subset_union_right
  have hXYU : X ∪ Y ⊆ U := Finset.subset_union_left
  obtain ⟨F, hFU, hFmem, hWcap, _⟩ :=
    exists_capStartPeel_of_oneChange_no_capSucc_no_cup (c := 5)
      (by decide) (by omega : 2 ≤ v) hone hnoCap hnoCup
  have hFX : F ⊆ X := by
    intro f hf
    obtain ⟨hfU, C, hCU, hCcard, hCcap, hfC, hCmin⟩ := (hFmem f).mp hf
    by_contra h
    have hfYZ : f ∈ Y ∪ Z := by
      rcases Finset.mem_union.mp hfU with hfXY | hfZ
      · exact Finset.mem_union_left _ ((Finset.mem_union.mp hfXY).resolve_left h)
      · exact Finset.mem_union_right _ hfZ
    apply hYZcap
    refine ⟨C, ?_, hCcard, hCcap⟩
    intro x hx
    rcases Finset.mem_union.mp (hCU hx) with hxXY | hxZ
    · rcases Finset.mem_union.mp hxXY with hxX | hxY
      · rcases Finset.mem_union.mp hfYZ with hfY | hfZ
        · have := hXY x hxX f hfY
          have := hCmin x hx
          omega
        · have := hXZ x hxX f hfZ
          have := hCmin x hx
          omega
      · exact Finset.mem_union_left _ hxY
    · exact Finset.mem_union_right _ hxZ
  let W := U \ F
  have hWU : W ⊆ U := Finset.sdiff_subset
  have hWcup : ¬ContainsCupSet χ W v :=
    fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hWU)
  obtain ⟨G, hGW, hGmem, hrestCap, hGcup⟩ :=
    exists_capStartPeel_of_oneChange_no_capSucc_no_cup (c := 4)
      (by decide) (by omega : 2 ≤ v) (hone.mono hWU) hWcap hWcup
  have hGxy : G ⊆ X ∪ Y := by
    intro g hg
    obtain ⟨hgW, C, hCW, hCcard, hCcap, hgC, hCmin⟩ := (hGmem g).mp hg
    by_contra h
    have hgZ : g ∈ Z := (Finset.mem_union.mp (hWU hgW)).resolve_left h
    apply hZcap
    refine ⟨C, ?_, hCcard, hCcap⟩
    intro x hx
    rcases Finset.mem_union.mp (hWU (hCW hx)) with hxXY | hxZ
    · rcases Finset.mem_union.mp hxXY with hxX | hxY
      · have := hXZ x hxX g hgZ
        have := hCmin x hx
        omega
      · have := hYZ x hxY g hgZ
        have := hCmin x hx
        omega
    · exact hxZ
  have hGcap : ¬ContainsCapSet χ G 5 :=
    fun h ↦ hWcap (FinsetPolygon.ContainsCapSet.mono h hGW)
  obtain ⟨H, hHG, hHmem, hmidCap, _⟩ :=
    exists_capStartPeel_of_oneChange_no_capSucc_no_cup (c := 4)
      (by decide) (by omega : 2 ≤ v - 1) (hone.mono (hGW.trans hWU)) hGcap hGcup
  have hHX : H ⊆ X := by
    intro h hh
    obtain ⟨hhG, C, hCG, hCcard, hCcap, hhC, hCmin⟩ := (hHmem h).mp hh
    by_contra hno
    have hhY : h ∈ Y := (Finset.mem_union.mp (hGxy hhG)).resolve_left hno
    apply hYcap
    refine ⟨C, ?_, hCcard, hCcap⟩
    intro x hx
    rcases Finset.mem_union.mp (hGxy (hCG hx)) with hxX | hxY
    · have := hXY x hxX h hhY
      have := hCmin x hx
      omega
    · exact hxY
  have hFHuX : F ∪ H ⊆ X := Finset.union_subset hFX hHX
  have hFHuU : F ∪ H ⊆ U := hFHuX.trans hXU
  have hFHcup : ¬ContainsCupSet χ (F ∪ H) (v - 1) := by
    rintro ⟨P, hPFH, hPcard, hPcup⟩
    have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
    let z := P.max' hPne
    have hzP : z ∈ P := Finset.max'_mem _ _
    have hPmax : ∀ x ∈ P, x ≤ z := fun x hx ↦ Finset.le_max' _ x hx
    have hPtwo : 2 ≤ P.card := by omega
    have hPU : P ⊆ U := hPFH.trans hFHuU
    have hPX : P ⊆ X := hPFH.trans hFHuX
    have hvarg : v - 1 + 1 = v := by omega
    rcases Finset.mem_union.mp (hPFH hzP) with hzF | hzH
    · obtain ⟨_, C, hCU, hCcard, hCcap, hzC, hCmin⟩ := (hFmem z).mp hzF
      have hPCU : P ∪ C ⊆ U := Finset.union_subset hPU hCU
      rcases containsCupSet_succ_or_containsCapSet_succ_of_oneChange_common_endpoint
          (hone.mono hPCU) hPtwo (by omega : 2 ≤ C.card) hzP hzC
          hPcup hCcap hPmax hCmin with hcup | hcap
      · exact hnoCup (by simpa only [hPcard, hvarg] using
          FinsetPolygon.ContainsCupSet.mono hcup hPCU)
      · exact hnoCap (by simpa only [hCcard, Nat.reduceAdd] using
          FinsetPolygon.ContainsCapSet.mono hcap hPCU)
    · obtain ⟨_, C, hCG, hCcard, hCcap, hzC, hCmin⟩ := (hHmem z).mp hzH
      have hCXY : C ⊆ X ∪ Y := hCG.trans hGxy
      have hPCXY : P ∪ C ⊆ X ∪ Y := Finset.union_subset
        (hPX.trans Finset.subset_union_left) hCXY
      have hPCU : P ∪ C ⊆ U := hPCXY.trans hXYU
      rcases containsCupSet_succ_or_containsCapSet_succ_of_oneChange_common_endpoint
          (hone.mono hPCU) hPtwo (by omega : 2 ≤ C.card) hzP hzC
          hPcup hCcap hPmax hCmin with hcup | hcap
      · exact hnoCup (by simpa only [hPcard, hvarg] using
          FinsetPolygon.ContainsCupSet.mono hcup hPCU)
      · exact hXYcap (by simpa only [hCcard, Nat.reduceAdd] using
          FinsetPolygon.ContainsCapSet.mono hcap hPCXY)
  have hFHcap : ¬ContainsCapSet χ (F ∪ H) 4 :=
    fun h ↦ hXcap (FinsetPolygon.ContainsCapSet.mono h hFHuX)
  have hFHbound := card_le_choose_of_oneChange_no_capFour_no_cup
    (hone.mono hFHuU) hFHcap hFHcup
  have hrestW : W \ G ⊆ W := Finset.sdiff_subset
  have hrestCup : ¬ContainsCupSet χ (W \ G) v :=
    fun h ↦ hWcup (FinsetPolygon.ContainsCupSet.mono h hrestW)
  have hrestBound := card_le_choose_of_oneChange_no_capFour_no_cup
    (hone.mono (hrestW.trans hWU)) hrestCap hrestCup
  have hmidG : G \ H ⊆ G := Finset.sdiff_subset
  have hmidCup : ¬ContainsCupSet χ (G \ H) (v - 1) :=
    fun h ↦ hGcup (FinsetPolygon.ContainsCupSet.mono h hmidG)
  have hmidBound := card_le_choose_of_oneChange_no_capFour_no_cup
    (hone.mono (hmidG.trans (hGW.trans hWU))) hmidCap hmidCup
  have hFHdis : Disjoint F H := by
    apply Finset.disjoint_left.mpr
    intro x hxF hxH
    exact (Finset.mem_sdiff.mp (hGW (hHG hxH))).2 hxF
  have hFHcard := Finset.card_union_of_disjoint hFHdis
  have hcard₁ : W.card + F.card = U.card :=
    Finset.card_sdiff_add_card_eq_card hFU
  have hcard₂ := Finset.card_sdiff_add_card_eq_card hGW
  have hcard₃ := Finset.card_sdiff_add_card_eq_card hHG
  constructor
  · change U.card ≤ _
    omega
  · intro hXcup
    have hFHcupSet : IsCupSet χ (F ∪ H) := FinsetPolygon.IsCupSet.mono hXcup hFHuX
    have hFHsmall : (F ∪ H).card < v - 1 := by
      by_contra h
      obtain ⟨D, hDFH, hDcard⟩ :=
        Finset.exists_subset_card_eq (by omega : v - 1 ≤ (F ∪ H).card)
      exact hFHcup ⟨D, hDFH, hDcard, FinsetPolygon.IsCupSet.mono hFHcupSet hDFH⟩
    change U.card ≤ _
    omega


end ErdosSzekeres
