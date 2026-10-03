import ESBlueprint.B.CardLeChooseAddChooseOfOneChangeGapNoCapSixNoCup
import ESBlueprint.B.MarkerCupEndpointsNoEndpointCapOnOneSide
import ESBlueprint.B.CardLeChooseOfOneChangeNoCapFourNoCup

namespace ErdosSzekeres

/-- Audited Marker6 cardinal bound with the required global six-cap exclusion retained. A complete first or last m-cup endpoint family is four-cap-free by strong marker exclusion, has at most choose(m,2) points and hits every m-cup. Z6 bounds its complement; Pascal gives two choose(m+1,3).
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_six_pred_pred_of_seven_le -/
theorem card_le_two_choose_cubic_of_oneChange_gap_no_capSix_straddled_cups {n m : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {q h : Fin n}
(hm : 3 ≤ m) (hq : q ∉ s) (hone : OneChangeOn χ s)
(hleft : ¬ContainsCapSet χ (s.filter (fun x ↦ x < q)) 5)
(hright : ¬ContainsCapSet χ (s.filter (fun x ↦ q < x)) 5)
(hnoCap : ¬ContainsCapSet χ s 6) (hnoCup : ¬ContainsCupSet χ s (m + 1))
(hstraddle : ∀ C : Finset (Fin n), C ⊆ s → C.card = m → IsCupSet χ C →
  (∃ x ∈ C, x < h) ∧ ∃ y ∈ C, h < y) :
s.card ≤ 2 * Nat.choose (m + 1) 3 := by
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
  have hcount (X : Finset (Fin n)) (hXs : X ⊆ s)
      (hXcap : ¬ContainsCapSet χ X 4)
      (hXside : (∀ x ∈ X, x < h) ∨ ∀ x ∈ X, h < x)
      (hXhit : ∀ C : Finset (Fin n), C ⊆ s → C.card = m → IsCupSet χ C →
        ∃ x ∈ C, x ∈ X) : s.card ≤ 2 * Nat.choose (m + 1) 3 := by
    have hXnoCup : ¬ContainsCupSet χ X m := by
      rintro ⟨C, hCX, hCcard, hCcup⟩
      have hspan := hstraddle C (hCX.trans hXs) hCcard hCcup
      rcases hXside with hXleft | hXright
      · obtain ⟨y, hy, hhy⟩ := hspan.2
        have := hXleft y (hCX hy)
        omega
      · obtain ⟨x, hx, hxh⟩ := hspan.1
        have := hXright x (hCX hx)
        omega
    have hXbound := card_le_choose_of_oneChange_no_capFour_no_cup
      (hone.mono hXs) hXcap hXnoCup
    have hrestSub : s \ X ⊆ s := Finset.sdiff_subset
    have hrestNoCup : ¬ContainsCupSet χ (s \ X) m := by
      rintro ⟨C, hCs, hCcard, hCcup⟩
      obtain ⟨x, hxC, hxX⟩ := hXhit C (hCs.trans hrestSub) hCcard hCcup
      exact (Finset.mem_sdiff.mp (hCs hxC)).2 hxX
    have hrestLeft : ¬ContainsCapSet χ ((s \ X).filter (fun x ↦ x < q)) 5 :=
      fun hcap ↦ hleft (FinsetPolygon.ContainsCapSet.mono hcap
        (Finset.filter_subset_filter _ hrestSub))
    have hrestRight : ¬ContainsCapSet χ ((s \ X).filter (fun x ↦ q < x)) 5 :=
      fun hcap ↦ hright (FinsetPolygon.ContainsCapSet.mono hcap
        (Finset.filter_subset_filter _ hrestSub))
    have hrestNoCap : ¬ContainsCapSet χ (s \ X) 6 :=
      fun hcap ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hrestSub)
    have hrestBound := card_le_choose_add_choose_of_oneChange_gap_no_capSix_no_cup
      (show 2 ≤ m by omega) (fun hqr ↦ hq (hrestSub hqr))
      (hone.mono hrestSub) hrestLeft hrestRight hrestNoCap hrestNoCup
    have hsplit := Finset.card_sdiff_add_card_eq_card hXs
    have hp : Nat.choose (m + 1) 3 = Nat.choose m 2 + Nat.choose m 3 := by
      simpa only [Nat.reduceAdd] using Nat.choose_succ_succ' m 2
    omega
  obtain hEfree | hFfree := markerCupEndpoints_no_endpoint_cap_on_one_side
    (a := 5) (b := 5) (by decide) (by decide) hm hq hone hleft hright
    hnoCup hstraddle hE hF
  · have hEno4 : ¬ContainsCapSet χ E 4 := by
      rintro ⟨K, hKE, hKcard, hKcap⟩
      have hne : K.Nonempty := Finset.card_pos.mp (by omega)
      let e := K.max' hne
      have heK : e ∈ K := Finset.max'_mem _ _
      exact hEfree ⟨K, e, hKE.trans (Finset.filter_subset _ _),
        by simpa using hKcard, hKcap, heK, hKE heK,
        fun x hx ↦ Finset.le_max' K x hx⟩
    exact hcount E (Finset.filter_subset _ _) hEno4 (Or.inl hEside) hEhit
  · have hFno4 : ¬ContainsCapSet χ F 4 := by
      rintro ⟨K, hKF, hKcard, hKcap⟩
      have hne : K.Nonempty := Finset.card_pos.mp (by omega)
      let f := K.min' hne
      have hfK : f ∈ K := Finset.min'_mem _ _
      exact hFfree ⟨K, f, hKF.trans (Finset.filter_subset _ _),
        by simpa using hKcard, hKcap, hfK, hKF hfK,
        fun x hx ↦ Finset.min'_le K x hx⟩
    exact hcount F (Finset.filter_subset _ _) hFno4 (Or.inr hFside) hFhit


end ErdosSzekeres
