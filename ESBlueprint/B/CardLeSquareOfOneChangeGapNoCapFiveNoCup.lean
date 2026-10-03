import ESBlueprint.B.CardLeChooseOfOneChangeNoCapFourNoCup
import ESBlueprint.B.MonochromaticSetInsertMaxOfOneChange

namespace ErdosSzekeres

/-- The classic Z bound: with four-cap-free sides of a missing gap, avoiding five-caps and v-cups bounds the set by (v-1)^2. The first points of four-caps and their complement admit complementary triangular bounds.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem card_le_square_of_oneChange_gap_no_capFive_no_cup {n v : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {q : Fin n} (hv : 2 ≤ v) (hq : q ∉ s) (hone : OneChangeOn χ s) (hleft : ¬ContainsCapSet χ (s.filter (fun x ↦ x < q)) 4) (hright : ¬ContainsCapSet χ (s.filter (fun x ↦ q < x)) 4) (hnoCap : ¬ContainsCapSet χ s 5) (hnoCup : ¬ContainsCupSet χ s v) : s.card ≤ (v - 1) ^ 2 := by
  classical
  let Z := s.filter (fun x ↦ ∃ C : Finset (Fin n),
    C ⊆ s ∧ C.card = 4 ∧ IsCapSet χ C ∧ x ∈ C ∧ ∀ y ∈ C, x ≤ y)
  have hZsub : Z ⊆ s := Finset.filter_subset _ _
  have hZleft : Z ⊆ s.filter (fun x ↦ x < q) := by
    intro z hz
    obtain ⟨hzS, C, hCsub, hCcard, hCcap, hzC, hCmin⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hzS, ?_⟩
    by_contra h
    apply hright
    refine ⟨C, ?_, hCcard, hCcap⟩
    intro y hy
    refine Finset.mem_filter.mpr ⟨hCsub hy, ?_⟩
    have hzy := hCmin y hy
    have hyq : y ≠ q := by
      intro heq
      exact hq (heq ▸ hCsub hy)
    omega
  have hZnoCap : ¬ContainsCapSet χ Z 4 := by
    intro h
    exact hleft (FinsetPolygon.ContainsCapSet.mono h hZleft)
  have hrestSub : s \ Z ⊆ s := Finset.sdiff_subset
  have hrestNoCap : ¬ContainsCapSet χ (s \ Z) 4 := by
    rintro ⟨C, hCsub, hCcard, hCcap⟩
    have hCne : C.Nonempty := by
      rw [← Finset.card_pos, hCcard]
      decide
    let x := C.min' hCne
    have hxC : x ∈ C := Finset.min'_mem _ _
    have hxrest := Finset.mem_sdiff.mp (hCsub hxC)
    apply hxrest.2
    refine Finset.mem_filter.mpr ⟨hxrest.1, C, hCsub.trans hrestSub,
      hCcard, hCcap, hxC, ?_⟩
    intro y hy
    exact Finset.min'_le _ y hy
  have hsmall : ∀ (A : Finset (Fin n)), A.card ≤ 2 → IsCupSet χ A := by
    intro A hA t hi hj hk
    exfalso
    have hsub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ A := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi, hj, hk⟩
    have hcard : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
      simp [ne_of_lt t.hij, ne_of_lt t.hjk, ne_of_lt (t.hij.trans t.hjk)]
    have := Finset.card_le_card hsub
    omega
  have hZnoCup : ¬ContainsCupSet χ Z (v - 1) := by
    rintro ⟨P, hPsub, hPcard, hPcup⟩
    have hPne : P.Nonempty := by
      rw [← Finset.card_pos, hPcard]
      omega
    let z := P.max' hPne
    have hzP : z ∈ P := Finset.max'_mem _ _
    have hPmax : ∀ y ∈ P, y ≤ z := by
      intro y hy
      exact Finset.le_max' _ y hy
    obtain ⟨_, C, hCsub, hCcard, hCcap, hzC, hCmin⟩ :=
      Finset.mem_filter.mp (hPsub hzP)
    have hCrest : (C.erase z).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hzC, hCcard]
      decide
    let a := (C.erase z).min' hCrest
    have haErase : a ∈ C.erase z := Finset.min'_mem _ _
    have haC : a ∈ C := (Finset.mem_erase.mp haErase).2
    have hza : z < a := by
      have := hCmin a haC
      have := (Finset.mem_erase.mp haErase).1
      omega
    have hCnext : ∀ y ∈ C, z < y → a ≤ y := by
      intro y hy hzy
      exact Finset.min'_le _ y (Finset.mem_erase.mpr ⟨ne_of_gt hzy, hy⟩)
    have hPsubS : P ⊆ s := hPsub.trans hZsub
    have haNotP : a ∉ P := by
      intro haP
      have := hPmax a haP
      omega
    have hnewSub : insert a P ⊆ s :=
      Finset.insert_subset_iff.mpr ⟨hCsub haC, hPsubS⟩
    have hnewCard : (insert a P).card = v := by
      rw [Finset.card_insert_of_notMem haNotP, hPcard]
      omega
    by_cases hvTwo : v = 2
    · exact hnoCup ⟨insert a P, hnewSub, hnewCard, hsmall _ (by omega)⟩
    have hPrest : (P.erase z).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hzP, hPcard]
      omega
    let b := (P.erase z).max' hPrest
    have hbErase : b ∈ P.erase z := Finset.max'_mem _ _
    have hbP : b ∈ P := (Finset.mem_erase.mp hbErase).2
    have hbz : b < z := by
      have := hPmax b hbP
      have := (Finset.mem_erase.mp hbErase).1
      omega
    have hPprev : ∀ y ∈ P, y < z → y ≤ b := by
      intro y hy hyz
      exact Finset.le_max' _ y (Finset.mem_erase.mpr ⟨ne_of_lt hyz, hy⟩)
    cases hturn : χ ⟨b, z, a, hbz, hza⟩ with
    | left =>
      have hnewCup : IsCupSet χ (insert a P) :=
        monochromaticSet_insert_max_of_oneChange hbP hzP hbz hza hPmax hPprev
          hPcup (hone.mono hnewSub) hturn
      exact hnoCup ⟨insert a P, hnewSub, hnewCard, hnewCup⟩
    | right =>
      have hbNotC : b ∉ C := by
        intro hbC
        have := hCmin b hbC
        omega
      have hcapSub : insert b C ⊆ s :=
        Finset.insert_subset_iff.mpr ⟨hPsubS hbP, hCsub⟩
      have hnewCap : IsCapSet χ (insert b C) :=
        monochromaticSet_insert_min_of_oneChange hzC haC hza hbz hCmin hCnext
          hCcap (hone.mono hcapSub) hturn
      apply hnoCap
      refine ⟨insert b C, hcapSub, ?_, hnewCap⟩
      rw [Finset.card_insert_of_notMem hbNotC, hCcard]
  have hZbound := card_le_choose_of_oneChange_no_capFour_no_cup
    (hone.mono hZsub) hZnoCap hZnoCup
  have hrestNoCup : ¬ContainsCupSet χ (s \ Z) v := by
    intro h
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono h hrestSub)
  have hrestBound := card_le_choose_of_oneChange_no_capFour_no_cup
    (hone.mono hrestSub) hrestNoCap hrestNoCup
  have hsplit := Finset.card_sdiff_add_card_eq_card hZsub
  have hv₁ : v - 1 + 1 = v := by omega
  have hv₂ : v - 2 + 1 = v - 1 := by omega
  have hpascal : Nat.choose v 2 = (v - 1) + Nat.choose (v - 1) 2 := by
    simpa only [hv₁, Nat.choose_one_right] using Nat.choose_succ_succ' (v - 1) 1
  have hprod : (v - 1) * (v - 2) = Nat.choose (v - 1) 2 * 2 := by
    simpa only [hv₂, Nat.choose_one_right] using Nat.add_one_mul_choose_eq (v - 2) 1
  calc
    s.card ≤ Nat.choose (v - 1) 2 + Nat.choose v 2 := by omega
    _ = (v - 1) ^ 2 := by nlinarith

end ErdosSzekeres
