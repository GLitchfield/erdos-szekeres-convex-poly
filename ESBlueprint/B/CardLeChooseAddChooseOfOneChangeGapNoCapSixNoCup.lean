import ESBlueprint.B.CardLeChooseOfOneChangeNoCapNoCup

namespace ErdosSzekeres

/-- The audited Z6 bound for two five-cap-free gap sides of a six-cap-free one-change set avoiding v-cups, obtained by localizing first points of five-caps and applying the generic classical bound.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_six_pred_pred_of_seven_le -/
theorem card_le_choose_add_choose_of_oneChange_gap_no_capSix_no_cup {n v : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {q : Fin n} (hv : 2 ≤ v) (hq : q ∉ s) (hone : OneChangeOn χ s) (hleft : ¬ContainsCapSet χ (s.filter (fun x ↦ x < q)) 5) (hright : ¬ContainsCapSet χ (s.filter (fun x ↦ q < x)) 5) (hnoCap : ¬ContainsCapSet χ s 6) (hnoCup : ¬ContainsCupSet χ s v) : s.card ≤ Nat.choose (v + 1) 3 + Nat.choose v 3 := by
  classical
  by_cases hvTwo : v = 2
  · have hbound := card_le_choose_of_oneChange_no_cap_no_cup
      (c := 6) (v := 2) (by decide) (by decide) hone hnoCap (by simpa [hvTwo] using hnoCup)
    simpa [hvTwo] using hbound
  obtain ⟨Z, hZS, hZmem, hrestCap, hZcup⟩ :=
    exists_capStartPeel_of_oneChange_no_capSucc_no_cup (c := 5)
      (by decide) hv hone hnoCap hnoCup
  have hZleft : Z ⊆ s.filter (fun x ↦ x < q) := by
    intro z hz
    obtain ⟨hzS, C, hCs, hCcard, hCcap, hzC, hCmin⟩ := (hZmem z).mp hz
    refine Finset.mem_filter.mpr ⟨hzS, ?_⟩
    by_contra h
    apply hright
    refine ⟨C, ?_, hCcard, hCcap⟩
    intro x hx
    refine Finset.mem_filter.mpr ⟨hCs hx, ?_⟩
    have hxq : x ≠ q := by rintro rfl; exact hq (hCs hx)
    have := hCmin x hx
    omega
  have hZcap : ¬ContainsCapSet χ Z 5 :=
    fun h ↦ hleft (FinsetPolygon.ContainsCapSet.mono h hZleft)
  have hrestS : s \ Z ⊆ s := Finset.sdiff_subset
  have hrestCup : ¬ContainsCupSet χ (s \ Z) v :=
    fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hrestS)
  have hrestBound := card_le_choose_of_oneChange_no_cap_no_cup
    (by decide : 2 ≤ 5) hv (hone.mono hrestS) hrestCap hrestCup
  have hZbound := card_le_choose_of_oneChange_no_cap_no_cup
    (by decide : 2 ≤ 5) (by omega : 2 ≤ v - 1) (hone.mono hZS) hZcap hZcup
  have harg₁ : 5 + v - 4 = v + 1 := by omega
  have harg₂ : 5 + (v - 1) - 4 = v := by omega
  simp only [harg₁, harg₂, Nat.reduceSub] at hrestBound hZbound
  have hcard := Finset.card_sdiff_add_card_eq_card hZS
  omega


end ErdosSzekeres
