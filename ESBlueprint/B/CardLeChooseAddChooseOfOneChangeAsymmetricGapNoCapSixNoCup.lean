import ESBlueprint.B.CardLeChooseOfOneChangeNoCapNoCup

namespace ErdosSzekeres

/-- The audited asymmetric ZR bound for four-cap-free left and five-cap-free right gap sides in a six-cap-free one-change set, together with the sharper linear start-set bound when the left side is a cup.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_six_pred_pred_of_seven_le -/
theorem card_le_choose_add_choose_of_oneChange_asymmetric_gap_no_capSix_no_cup {n v : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {q : Fin n} (hv : 2 ≤ v) (hq : q ∉ s) (hone : OneChangeOn χ s) (hleft : ¬ContainsCapSet χ (s.filter (fun x ↦ x < q)) 4) (hright : ¬ContainsCapSet χ (s.filter (fun x ↦ q < x)) 5) (hnoCap : ¬ContainsCapSet χ s 6) (hnoCup : ¬ContainsCupSet χ s v) : s.card ≤ Nat.choose (v + 1) 3 + Nat.choose (v - 1) 2 ∧ (IsCupSet χ (s.filter (fun x ↦ x < q)) → s.card ≤ Nat.choose (v + 1) 3 + (v - 2)) := by
  classical
  by_cases hvTwo : v = 2
  · have hbound := card_le_choose_of_oneChange_no_cap_no_cup
      (c := 6) (v := 2) (by decide) (by decide) hone hnoCap (by simpa [hvTwo] using hnoCup)
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.choose_self] at hbound
    constructor
    · simpa [hvTwo] using hbound
    · intro _
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
  have hZcap : ¬ContainsCapSet χ Z 4 :=
    fun h ↦ hleft (FinsetPolygon.ContainsCapSet.mono h hZleft)
  have hrestS : s \ Z ⊆ s := Finset.sdiff_subset
  have hrestCup : ¬ContainsCupSet χ (s \ Z) v :=
    fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hrestS)
  have hrestBound := card_le_choose_of_oneChange_no_cap_no_cup
    (by decide : 2 ≤ 5) hv (hone.mono hrestS) hrestCap hrestCup
  have hZbound := card_le_choose_of_oneChange_no_cap_no_cup
    (by decide : 2 ≤ 4) (by omega : 2 ≤ v - 1) (hone.mono hZS) hZcap hZcup
  have harg₁ : 5 + v - 4 = v + 1 := by omega
  have harg₂ : 4 + (v - 1) - 4 = v - 1 := by omega
  simp only [harg₁, harg₂, Nat.reduceSub] at hrestBound hZbound
  have hcard := Finset.card_sdiff_add_card_eq_card hZS
  constructor
  · omega
  · intro hleftCup
    have hZcupSet : IsCupSet χ Z := FinsetPolygon.IsCupSet.mono hleftCup hZleft
    have hZsmall : Z.card < v - 1 := by
      by_contra h
      obtain ⟨D, hDZ, hDcard⟩ := Finset.exists_subset_card_eq (by omega : v - 1 ≤ Z.card)
      exact hZcup ⟨D, hDZ, hDcard, FinsetPolygon.IsCupSet.mono hZcupSet hDZ⟩
    omega


end ErdosSzekeres
