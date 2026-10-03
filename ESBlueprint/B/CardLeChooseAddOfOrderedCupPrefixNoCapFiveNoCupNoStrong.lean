import ESBlueprint.B.CardLtChooseOfOrderedCupPrefixNoCapFiveNoCupNoStrong
import ESBlueprint.B.CardLeChooseOfOneChangeNoCapFourNoCup

namespace ErdosSzekeres

/-- An ordered cup prefix and four-cap-free suffix have cardinality at most choose m 2 plus m-3 under one-change and avoidance of five-caps, m-cups and strong m+1-sets. Moving a full prefix maximum into the suffix reduces to the certified strict top-row deficit.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem card_le_choose_add_of_ordered_cup_prefix_no_capFive_no_cup_no_strong {n m : ℕ} {χ : TripleColoring n} {P Q : Finset (Fin n)} (hm : 4 ≤ m) (hsep : ∀ x ∈ P, ∀ y ∈ Q, x < y) (hPcup : IsCupSet χ P) (hone : OneChangeOn χ (P ∪ Q)) (hQnoCap : ¬ContainsCapSet χ Q 4) (hnoCap : ¬ContainsCapSet χ (P ∪ Q) 5) (hnoCup : ¬ContainsCupSet χ (P ∪ Q) m) (hnoStrong : ¬ContainsStrongPolygonSet χ (P ∪ Q) (m + 1)) : P.card + Q.card ≤ Nat.choose m 2 + (m - 3) := by
  classical
  let S := P ∪ Q
  have hPsub : P ⊆ S := Finset.subset_union_left
  have hQsub : Q ⊆ S := Finset.subset_union_right
  have hPsmall : P.card < m := by
    by_contra h
    obtain ⟨A, hAP, hAcard⟩ := Finset.exists_subset_card_eq (show m ≤ P.card by omega)
    exact hnoCup ⟨A, hAP.trans hPsub, hAcard, FinsetPolygon.IsCupSet.mono hPcup hAP⟩
  have hQbound : Q.card ≤ Nat.choose m 2 := card_le_choose_of_oneChange_no_capFour_no_cup
    (hone.mono hQsub) hQnoCap (fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hQsub))
  by_cases hshort : P.card ≤ m - 3
  · omega
  by_cases hmid : P.card = m - 2
  · have hstrict := card_lt_choose_of_ordered_cup_prefix_no_capFive_no_cup_no_strong
      hm hsep hmid hPcup hone hQnoCap hnoCap hnoCup hnoStrong
    omega
  have hPcard : P.card = m - 1 := by omega
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  let p := P.max' hPne
  have hpP : p ∈ P := Finset.max'_mem _ _
  have hpmax : ∀ x ∈ P, x ≤ p := fun x hx ↦ Finset.le_max' _ x hx
  let Z := P.erase p
  let W := insert p Q
  have hZcard : Z.card = m - 2 := by
    dsimp [Z]
    rw [Finset.card_erase_of_mem hpP, hPcard]
    omega
  have hZsubP : Z ⊆ P := Finset.erase_subset _ _
  have hZsub : Z ⊆ S := hZsubP.trans hPsub
  have hZcup : IsCupSet χ Z := FinsetPolygon.IsCupSet.mono hPcup hZsubP
  have hunion : Z ∪ W = S := by
    dsimp [Z, W, S]
    rw [← Finset.insert_union_comm, Finset.insert_erase hpP]
  have hWsub : W ⊆ S := by
    rw [← hunion]
    exact Finset.subset_union_right
  have hsepZW : ∀ x ∈ Z, ∀ y ∈ W, x < y := by
    intro x hx y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · have := hpmax x (hZsubP hx)
      have := (Finset.mem_erase.mp hx).1
      omega
    · exact hsep x (hZsubP hx) y hy
  have hZne : Z.Nonempty := Finset.card_pos.mp (by omega)
  let z := Z.max' hZne
  have hzZ : z ∈ Z := Finset.max'_mem _ _
  have hzP : z ∈ P := hZsubP hzZ
  have hzp : z < p := hsepZW z hzZ p (by simp [W])
  have hzprev : ∀ x ∈ P, x < p → x ≤ z := by
    intro x hx hxp
    exact Finset.le_max' _ x (Finset.mem_erase.mpr ⟨ne_of_lt hxp, hx⟩)
  have hWnoCap : ¬ContainsCapSet χ W 4 := by
    rintro ⟨C, hCsub, hCcard, hCcap⟩
    have hpC : p ∈ C := by
      by_contra hpNot
      apply hQnoCap
      refine ⟨C, ?_, hCcard, hCcap⟩
      intro x hx
      rcases Finset.mem_insert.mp (hCsub hx) with rfl | hxQ
      · exact (hpNot hx).elim
      · exact hxQ
    have hpmin : ∀ x ∈ C, p ≤ x := by
      intro x hx
      rcases Finset.mem_insert.mp (hCsub hx) with rfl | hxQ
      · exact le_rfl
      · exact (hsep p hpP x hxQ).le
    have hrest : (C.erase p).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hpC, hCcard]
      decide
    let a := (C.erase p).min' hrest
    have haErase : a ∈ C.erase p := Finset.min'_mem _ _
    have haC : a ∈ C := (Finset.mem_erase.mp haErase).2
    have hpa : p < a := by
      have := hpmin a haC
      have := (Finset.mem_erase.mp haErase).1
      omega
    have hanext : ∀ x ∈ C, p < x → a ≤ x := by
      intro x hx hpx
      exact Finset.min'_le _ x (Finset.mem_erase.mpr ⟨ne_of_gt hpx, hx⟩)
    cases hturn : χ ⟨z, p, a, hzp, hpa⟩ with
    | left =>
      have hsub : insert a P ⊆ S :=
        Finset.insert_subset_iff.mpr ⟨hWsub (hCsub haC), hPsub⟩
      have hcup := monochromaticSet_insert_max_of_oneChange hzP hpP hzp hpa
        hpmax hzprev hPcup (hone.mono hsub) hturn
      have haNotP : a ∉ P := by
        intro hx
        have := hpmax a hx
        omega
      exact hnoCup ⟨insert a P, hsub, by rw [Finset.card_insert_of_notMem haNotP, hPcard]; omega,
        hcup⟩
    | right =>
      have hsub : insert z C ⊆ S :=
        Finset.insert_subset_iff.mpr ⟨hZsub hzZ, hCsub.trans hWsub⟩
      have hcap := monochromaticSet_insert_min_of_oneChange hpC haC hpa hzp
        hpmin hanext hCcap (hone.mono hsub) hturn
      have hzNotC : z ∉ C := by
        intro hx
        have := hpmin z hx
        omega
      exact hnoCap ⟨insert z C, hsub, by rw [Finset.card_insert_of_notMem hzNotC, hCcard], hcap⟩
  have hstrict := card_lt_choose_of_ordered_cup_prefix_no_capFive_no_cup_no_strong
    hm hsepZW hZcard hZcup (by rw [hunion]; exact hone) hWnoCap
    (by rw [hunion]; exact hnoCap) (by rw [hunion]; exact hnoCup)
    (by rw [hunion]; exact hnoStrong)
  have hpNotQ : p ∉ Q := by
    intro hx
    have := hsep p hpP p hx
    omega
  have hWcard : W.card = Q.card + 1 := Finset.card_insert_of_notMem hpNotQ
  omega

end ErdosSzekeres
