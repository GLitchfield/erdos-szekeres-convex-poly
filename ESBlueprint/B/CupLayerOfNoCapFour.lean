import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- L1: in any OneChange coloring avoiding a four-cap, every fiber of an exact longest-ending-cup rank profile is a cup with at most its rank many points. The profile is specified by attained ending cups and maximality over all ending cups; no computational rank assumption is hidden.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq, ErdosSzekeres.isMonochromaticChain_finFour_of_outer_eq
@dangling-ok Approved R20 reusable layer tool for cap-free sides in a≥5 two-side bounds and cross-gap layer arguments; coupled cut remains open -/
theorem cupLayer_of_no_capFour {n j : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (rank : Fin n → ℕ)
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4)
    (hattain : ∀ x ∈ s, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = rank x ∧
      IsCupSet χ C ∧ x ∈ C ∧ (∀ y ∈ C, y ≤ x))
    (hmax : ∀ x ∈ s, ∀ C : Finset (Fin n), C ⊆ s → IsCupSet χ C →
      x ∈ C → (∀ y ∈ C, y ≤ x) → C.card ≤ rank x) :
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
  -- A cup extends at its maximum when the new final consecutive turn is a cup.
  have append {C : Finset (Fin n)} {w x y : Fin n}
      (hCsub : C ⊆ s) (hcup : IsCupSet χ C) (hx : x ∈ C) (hw : w ∈ C)
      (hwx : w < x) (hxy : x < y) (hy : y ∈ s)
      (hend : ∀ a ∈ C, a ≤ x) (hprev : ∀ a ∈ C, a < x → a ≤ w)
      (hturn : χ ⟨w, x, y, hwx, hxy⟩ = Turn.left) :
      IsCupSet χ (insert y C) := by
    have endpointTurn (a : Fin n) (ha : a ∈ C) (hax : a < x) :
        χ ⟨a, x, y, hax, hxy⟩ = Turn.left := by
      rcases eq_or_lt_of_le (hprev a ha hax) with rfl | haw
      · exact hturn
      · have hfirst := hcup ⟨a, w, x, haw, hwx⟩ ha hw hx
        have hseq := hone haw hwx hxy (hCsub ha) (hCsub hw) (hCsub hx) hy
        have hall := hseq.all_eq_of_outer_eq (hfirst.trans hturn.symm)
        exact hall.2.2.trans hturn
    intro t hi hj hk
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = Turn.left
    by_cases hky : t.k = y
    · have hiNot : t.i ≠ y := by
        rw [← hky]
        exact ne_of_lt (t.hij.trans t.hjk)
      have hjNot : t.j ≠ y := by
        rw [← hky]
        exact ne_of_lt t.hjk
      have hiC : t.i ∈ C := by simpa [hiNot] using hi
      have hjC : t.j ∈ C := by simpa [hjNot] using hj
      rcases eq_or_lt_of_le (hend t.j hjC) with hjx | hjx
      · have hix : t.i < x := by simpa [hjx] using t.hij
        simpa [hky, hjx] using endpointTurn t.i hiC hix
      · have hfirst := hcup ⟨t.i, t.j, x, t.hij, hjx⟩ hiC hjC hx
        have hlast := endpointTurn t.j hjC hjx
        have hseq := hone t.hij hjx hxy (hCsub hiC) (hCsub hjC) (hCsub hx) hy
        have hall := hseq.all_eq_of_outer_eq (hfirst.trans hlast.symm)
        simpa [hky] using hall.1.symm.trans hfirst
    · have hkC : t.k ∈ C := by simpa [hky] using hk
      have hkyLt : t.k < y := (hend t.k hkC).trans_lt hxy
      have hiC : t.i ∈ C := by
        simpa [ne_of_lt (t.hij.trans (t.hjk.trans hkyLt))] using hi
      have hjC : t.j ∈ C := by simpa [ne_of_lt (t.hjk.trans hkyLt)] using hj
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
    obtain ⟨hiS, hiRank⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjS, hjRank⟩ := Finset.mem_filter.mp hj
    obtain ⟨hkS, _⟩ := Finset.mem_filter.mp hk
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = Turn.left
    cases hcol : χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ with
    | left => rfl
    | right =>
        apply False.elim
        have hpairSub : ({t.i, t.j} : Finset (Fin n)) ⊆ s := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hiS
          · exact hjS
        have hpairEnd : ∀ z ∈ ({t.i, t.j} : Finset (Fin n)), z ≤ t.j := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact t.hij.le
          · exact le_rfl
        have hpairMax := hmax t.j hjS {t.i, t.j} hpairSub (cupTwo t.i t.j)
          (by simp) hpairEnd
        have hjTwo : 2 ≤ j := by simpa [ne_of_lt t.hij, hjRank] using hpairMax
        obtain ⟨C, hCsub, hCcard, hCcup, hxC, hend⟩ := hattain t.i hiS
        have hCj : C.card = j := hCcard.trans hiRank
        have hErase := Finset.card_erase_add_one hxC
        have hne : (C.erase t.i).Nonempty := Finset.card_pos.mp (by omega)
        let w := (C.erase t.i).max' hne
        have hwErase : w ∈ C.erase t.i := Finset.max'_mem _ hne
        obtain ⟨hwNe, hwC⟩ := Finset.mem_erase.mp hwErase
        have hwx : w < t.i := by
          have hwLe := hend w hwC
          omega
        have hprev : ∀ a ∈ C, a < t.i → a ≤ w := by
          intro a ha hax
          exact Finset.le_max' _ a (Finset.mem_erase.mpr ⟨ne_of_lt hax, ha⟩)
        cases hwcol : χ ⟨w, t.i, t.j, hwx, t.hij⟩ with
        | left =>
            have hnewCup := append hCsub hCcup hxC hwC hwx t.hij hjS hend hprev hwcol
            have hyNot : t.j ∉ C := fun hmem =>
              (not_le_of_gt t.hij) (hend t.j hmem)
            have hnewCard : (insert t.j C).card = j + 1 := by
              rw [Finset.card_insert_of_notMem hyNot, hCj]
            have hnewSub : insert t.j C ⊆ s := Finset.insert_subset_iff.mpr ⟨hjS, hCsub⟩
            have hnewEnd : ∀ a ∈ insert t.j C, a ≤ t.j := by
              intro a ha
              rcases Finset.mem_insert.mp ha with rfl | ha
              · exact le_rfl
              · exact (hend a ha).trans t.hij.le
            have hnewMax := hmax t.j hjS (insert t.j C) hnewSub hnewCup (by simp) hnewEnd
            rw [hnewCard, hjRank] at hnewMax
            omega
        | right =>
            exact hnoCap (fourCap hwx t.hij t.hjk (hCsub hwC) hiS hjS hkS hwcol hcol)
  refine ⟨hLcup, ?_⟩
  by_cases hne : L.Nonempty
  · let y := L.max' hne
    have hyL : y ∈ L := Finset.max'_mem L hne
    have hyRank : rank y = j := (Finset.mem_filter.mp hyL).2
    have hbound := hmax y (hLsub hyL) L hLsub hLcup hyL
      (fun z hz => Finset.le_max' L z hz)
    simpa [hyRank] using hbound
  · have hcard : L.card = 0 := by
      by_contra hcard
      exact hne (Finset.card_pos.mp (by omega))
    omega

end ErdosSzekeres
