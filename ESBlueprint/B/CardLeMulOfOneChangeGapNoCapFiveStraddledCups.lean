import ESBlueprint.B.MarkerCupEndpointsNoCapThreeOnOneSide
import ESBlueprint.B.CardLeSquareOfOneChangeGapNoCapFiveNoCup
import ESBlueprint.B.IsCupSetIffNotContainsCapSetThree

namespace ErdosSzekeres

/-- The audited marker bound: a one-change five-cap-free set with four-cap-free sides at a missing gap and every m-cup straddling a possibly different marker has at most m times m-1 points. A complete endpoint family is a cup of at most m-1 points, and deleting it leaves an m-cup-free set bounded by the classic square estimate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem card_le_mul_of_oneChange_gap_no_capFive_straddled_cups {n m : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {q h : Fin n} (hm : 3 ≤ m) (hq : q ∉ s) (hone : OneChangeOn χ s) (hleft : ¬ContainsCapSet χ (s.filter (fun x ↦ x < q)) 4) (hright : ¬ContainsCapSet χ (s.filter (fun x ↦ q < x)) 4) (hnoCap : ¬ContainsCapSet χ s 5) (hnoCup : ¬ContainsCupSet χ s (m + 1)) (hstraddle : ∀ C : Finset (Fin n), C ⊆ s → C.card = m → IsCupSet χ C → (∃ x ∈ C, x < h) ∧ ∃ y ∈ C, h < y) : s.card ≤ m * (m - 1) := by
  classical
  let E := s.filter (fun e ↦ ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = m ∧
    IsCupSet χ C ∧ e ∈ C ∧ ∀ x ∈ C, e ≤ x)
  let F := s.filter (fun f ↦ ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = m ∧
    IsCupSet χ C ∧ f ∈ C ∧ ∀ x ∈ C, x ≤ f)
  have hE : ∀ e ∈ E, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = m ∧
      IsCupSet χ C ∧ e ∈ C ∧ ∀ x ∈ C, e ≤ x :=
    fun _ he ↦ (Finset.mem_filter.mp he).2
  have hF : ∀ f ∈ F, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = m ∧
      IsCupSet χ C ∧ f ∈ C ∧ ∀ x ∈ C, x ≤ f :=
    fun _ hf ↦ (Finset.mem_filter.mp hf).2
  have hEside : ∀ e ∈ E, e < h := by
    intro e he
    obtain ⟨C, hCs, hCcard, hCcup, _, hemin⟩ := hE e he
    obtain ⟨x, hx, hxh⟩ := (hstraddle C hCs hCcard hCcup).1
    exact (hemin x hx).trans_lt hxh
  have hFside : ∀ f ∈ F, h < f := by
    intro f hf
    obtain ⟨C, hCs, hCcard, hCcup, _, hfmax⟩ := hF f hf
    obtain ⟨x, hx, hhx⟩ := (hstraddle C hCs hCcard hCcup).2
    exact hhx.trans_le (hfmax x hx)
  have hEhit : ∀ C : Finset (Fin n), C ⊆ s → C.card = m → IsCupSet χ C →
      ∃ x ∈ C, x ∈ E := by
    intro C hCs hCcard hCcup
    have hne : C.Nonempty := Finset.card_pos.mp (by omega)
    let e := C.min' hne
    have heC : e ∈ C := Finset.min'_mem _ _
    refine ⟨e, heC, Finset.mem_filter.mpr ⟨hCs heC, ?_⟩⟩
    exact ⟨C, hCs, hCcard, hCcup, heC, fun x hx ↦ Finset.min'_le C x hx⟩
  have hFhit : ∀ C : Finset (Fin n), C ⊆ s → C.card = m → IsCupSet χ C →
      ∃ x ∈ C, x ∈ F := by
    intro C hCs hCcard hCcup
    have hne : C.Nonempty := Finset.card_pos.mp (by omega)
    let f := C.max' hne
    have hfC : f ∈ C := Finset.max'_mem _ _
    refine ⟨f, hfC, Finset.mem_filter.mpr ⟨hCs hfC, ?_⟩⟩
    exact ⟨C, hCs, hCcard, hCcup, hfC, fun x hx ↦ Finset.le_max' C x hx⟩
  have hcount (X : Finset (Fin n)) (hXsub : X ⊆ s) (hXcup : IsCupSet χ X)
      (hXside : (∀ x ∈ X, x < h) ∨ ∀ x ∈ X, h < x)
      (hXhit : ∀ C : Finset (Fin n), C ⊆ s → C.card = m → IsCupSet χ C →
        ∃ x ∈ C, x ∈ X) : s.card ≤ m * (m - 1) := by
    have hXsmall : X.card < m := by
      by_contra hlarge
      obtain ⟨C, hCX, hCcard⟩ := Finset.exists_subset_card_eq (show m ≤ X.card by omega)
      have hCcup : IsCupSet χ C := FinsetPolygon.IsCupSet.mono hXcup hCX
      have hspan := hstraddle C (hCX.trans hXsub) hCcard hCcup
      rcases hXside with hleftX | hrightX
      · obtain ⟨y, hy, hhy⟩ := hspan.2
        have := hleftX y (hCX hy)
        omega
      · obtain ⟨x, hx, hxh⟩ := hspan.1
        have := hrightX x (hCX hx)
        omega
    have hrestSub : s \ X ⊆ s := Finset.sdiff_subset
    have hrestNoCup : ¬ContainsCupSet χ (s \ X) m := by
      rintro ⟨C, hCs, hCcard, hCcup⟩
      obtain ⟨x, hxC, hxX⟩ := hXhit C (hCs.trans hrestSub) hCcard hCcup
      exact (Finset.mem_sdiff.mp (hCs hxC)).2 hxX
    have hrestLeft : ¬ContainsCapSet χ ((s \ X).filter (fun x ↦ x < q)) 4 := by
      intro hcap
      exact hleft (FinsetPolygon.ContainsCapSet.mono hcap
        (Finset.filter_subset_filter _ hrestSub))
    have hrestRight : ¬ContainsCapSet χ ((s \ X).filter (fun x ↦ q < x)) 4 := by
      intro hcap
      exact hright (FinsetPolygon.ContainsCapSet.mono hcap
        (Finset.filter_subset_filter _ hrestSub))
    have hrestNoCap : ¬ContainsCapSet χ (s \ X) 5 :=
      fun hcap ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hrestSub)
    have hrestBound := card_le_square_of_oneChange_gap_no_capFive_no_cup
      (show 2 ≤ m by omega) (fun hqr ↦ hq (hrestSub hqr))
      (hone.mono hrestSub) hrestLeft hrestRight hrestNoCap hrestNoCup
    have hsplit := Finset.card_sdiff_add_card_eq_card hXsub
    have hpred : m - 1 + 1 = m := by omega
    have harith : (m - 1) ^ 2 + (m - 1) = m * (m - 1) := by
      calc
        (m - 1) ^ 2 + (m - 1) = (m - 1 + 1) * (m - 1) := by ring
        _ = m * (m - 1) := by rw [hpred]
    omega
  obtain hEfree | hFfree := markerCupEndpoints_no_capThree_on_one_side
    hm hq hone hleft hright hnoCup hstraddle hE hF
  · exact hcount E (Finset.filter_subset _ _)
      (isCupSet_iff_not_containsCapSet_three.mpr hEfree) (Or.inl hEside) hEhit
  · exact hcount F (Finset.filter_subset _ _)
      (isCupSet_iff_not_containsCapSet_three.mpr hFfree) (Or.inr hFside) hFhit

end ErdosSzekeres
