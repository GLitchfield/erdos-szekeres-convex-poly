import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- Starting-layer mirror of L1: under OneChange and no four-cap, each exact longest-starting-cup rank fiber is a cup with at most its rank many points. Profiles are explicitly attained and maximal over endpoint-containing starting cups.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq, ErdosSzekeres.isMonochromaticChain_finFour_of_outer_eq
@dangling-ok Approved R20 reusable mirrored layer tool for both cap-free gap sides and cross-gap a5 arguments; coupled cut remains open -/
theorem startingCupLayer_of_no_capFour {n j : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (rank : Fin n → ℕ)
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4)
    (hattain : ∀ x ∈ s, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = rank x ∧
      IsCupSet χ C ∧ x ∈ C ∧ (∀ y ∈ C, x ≤ y))
    (hmax : ∀ x ∈ s, ∀ C : Finset (Fin n), C ⊆ s → IsCupSet χ C →
      x ∈ C → (∀ y ∈ C, x ≤ y) → C.card ≤ rank x) :
    IsCupSet χ (s.filter (fun x => rank x = j)) ∧
      (s.filter (fun x => rank x = j)).card ≤ j := by
  classical
  have cupTwo (a b : Fin n) : IsCupSet χ ({a, b} : Finset (Fin n)) := by
    intro t hi hj hk
    have hij := t.hij
    have hjk := t.hjk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with hi | hi <;> rcases hj with hj | hj <;>
      rcases hk with hk | hk <;> omega
  -- A cup extends at its minimum when the new first consecutive turn is a cup.
  have prepend {C : Finset (Fin n)} {y x w : Fin n}
      (hCsub : C ⊆ s) (hcup : IsCupSet χ C) (hx : x ∈ C) (hw : w ∈ C)
      (hyx : y < x) (hxw : x < w) (hy : y ∈ s)
      (hstart : ∀ a ∈ C, x ≤ a) (hnext : ∀ a ∈ C, x < a → w ≤ a)
      (hturn : χ ⟨y, x, w, hyx, hxw⟩ = Turn.left) :
      IsCupSet χ (insert y C) := by
    have endpointTurn (a : Fin n) (ha : a ∈ C) (hxa : x < a) :
        χ ⟨y, x, a, hyx, hxa⟩ = Turn.left := by
      rcases eq_or_lt_of_le (hnext a ha hxa) with rfl | hwa
      · exact hturn
      · have hlast := hcup ⟨x, w, a, hxw, hwa⟩ hx hw ha
        have hseq := hone hyx hxw hwa hy (hCsub hx) (hCsub hw) (hCsub ha)
        have hall := hseq.all_eq_of_outer_eq (hturn.trans hlast.symm)
        exact hall.1.symm.trans hturn
    intro t hi hj hk
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = Turn.left
    by_cases hiy : t.i = y
    · have hjNot : t.j ≠ y := by
        rw [← hiy]
        exact ne_of_gt t.hij
      have hkNot : t.k ≠ y := by
        rw [← hiy]
        exact ne_of_gt (t.hij.trans t.hjk)
      have hjC : t.j ∈ C := by simpa [hjNot] using hj
      have hkC : t.k ∈ C := by simpa [hkNot] using hk
      rcases eq_or_lt_of_le (hstart t.j hjC) with hxj | hxj
      · have hxk : x < t.k := by simpa [hxj] using t.hjk
        simpa [hiy, hxj] using endpointTurn t.k hkC hxk
      · have hfirst := endpointTurn t.j hjC hxj
        have hlast := hcup ⟨x, t.j, t.k, hxj, t.hjk⟩ hx hjC hkC
        have hseq := hone hyx hxj t.hjk hy (hCsub hx) (hCsub hjC) (hCsub hkC)
        have hall := hseq.all_eq_of_outer_eq (hfirst.trans hlast.symm)
        simpa [hiy] using hall.2.2.trans hlast
    · have hiC : t.i ∈ C := by simpa [hiy] using hi
      have hyiLt : y < t.i := hyx.trans_le (hstart t.i hiC)
      have hjC : t.j ∈ C := by simpa [ne_of_gt (hyiLt.trans t.hij)] using hj
      have hkC : t.k ∈ C := by
        simpa [ne_of_gt (hyiLt.trans (t.hij.trans t.hjk))] using hk
      exact hcup t hiC hjC hkC
  have fourCap {a b c d : Fin n}
      (hab : a < b) (hbc : b < c) (hcd : c < d)
      (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
      (hfirst : χ ⟨a, b, c, hab, hbc⟩ = Turn.right)
      (hlast : χ ⟨b, c, d, hbc, hcd⟩ = Turn.right) :
      ContainsCapSet χ s 4 := by
    let f : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono ![a, b, c, d] (by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · simpa using hab
      · simpa using hbc
      · simpa using hcd)
    have hsub : Finset.univ.image f ⊆ s := by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
      obtain ⟨i, rfl⟩ := hz
      fin_cases i
      · simpa [f] using ha
      · simpa [f] using hb
      · simpa [f] using hc
      · simpa [f] using hd
    refine ⟨Finset.univ.image f, hsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · exact FinsetPolygon.IsCap.image (isMonochromaticChain_finFour_of_outer_eq f
        (hone.mono hsub) (by simpa [f] using hfirst) (by simpa [f] using hlast))
  let L := s.filter (fun x => rank x = j)
  change IsCupSet χ L ∧ L.card ≤ j
  have hLsub : L ⊆ s := Finset.filter_subset _ _
  have hLcup : IsCupSet χ L := by
    intro t hi hj hk
    obtain ⟨hiS, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjS, hjRank⟩ := Finset.mem_filter.mp hj
    obtain ⟨hkS, hkRank⟩ := Finset.mem_filter.mp hk
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = Turn.left
    cases hcol : χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ with
    | left => rfl
    | right =>
        apply False.elim
        have hpairSub : ({t.j, t.k} : Finset (Fin n)) ⊆ s := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hjS
          · exact hkS
        have hpairStart : ∀ z ∈ ({t.j, t.k} : Finset (Fin n)), t.j ≤ z := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact le_rfl
          · exact t.hjk.le
        have hpairMax := hmax t.j hjS {t.j, t.k} hpairSub (cupTwo t.j t.k)
          (by simp) hpairStart
        have hjTwo : 2 ≤ j := by simpa [ne_of_lt t.hjk, hjRank] using hpairMax
        obtain ⟨C, hCsub, hCcard, hCcup, hxC, hstart⟩ := hattain t.k hkS
        have hCj : C.card = j := hCcard.trans hkRank
        have hErase := Finset.card_erase_add_one hxC
        have hne : (C.erase t.k).Nonempty := Finset.card_pos.mp (by omega)
        let w := (C.erase t.k).min' hne
        have hwErase : w ∈ C.erase t.k := Finset.min'_mem _ hne
        obtain ⟨hwNe, hwC⟩ := Finset.mem_erase.mp hwErase
        have hxw : t.k < w := by
          have hwLe := hstart w hwC
          omega
        have hnext : ∀ a ∈ C, t.k < a → w ≤ a := by
          intro a ha hxa
          exact Finset.min'_le _ a (Finset.mem_erase.mpr ⟨ne_of_gt hxa, ha⟩)
        cases hwcol : χ ⟨t.j, t.k, w, t.hjk, hxw⟩ with
        | left =>
            have hnewCup := prepend hCsub hCcup hxC hwC t.hjk hxw hjS hstart hnext hwcol
            have hyNot : t.j ∉ C := fun hmem =>
              (not_le_of_gt t.hjk) (hstart t.j hmem)
            have hnewCard : (insert t.j C).card = j + 1 := by
              rw [Finset.card_insert_of_notMem hyNot, hCj]
            have hnewSub : insert t.j C ⊆ s := Finset.insert_subset_iff.mpr ⟨hjS, hCsub⟩
            have hnewStart : ∀ a ∈ insert t.j C, t.j ≤ a := by
              intro a ha
              rcases Finset.mem_insert.mp ha with rfl | ha
              · exact le_rfl
              · exact t.hjk.le.trans (hstart a ha)
            have hnewMax := hmax t.j hjS (insert t.j C) hnewSub hnewCup (by simp) hnewStart
            rw [hnewCard, hjRank] at hnewMax
            omega
        | right =>
            exact hnoCap (fourCap t.hij t.hjk hxw hiS hjS hkS (hCsub hwC) hcol hwcol)
  refine ⟨hLcup, ?_⟩
  by_cases hne : L.Nonempty
  · let y := L.min' hne
    have hyL : y ∈ L := Finset.min'_mem L hne
    have hyRank : rank y = j := (Finset.mem_filter.mp hyL).2
    have hbound := hmax y (hLsub hyL) L hLsub hLcup hyL
      (fun z hz => Finset.min'_le L z hz)
    simpa [hyRank] using hbound
  · have hcard : L.card = 0 := by
      by_contra hcard
      exact hne (Finset.card_pos.mp (by omega))
    omega


end ErdosSzekeres
