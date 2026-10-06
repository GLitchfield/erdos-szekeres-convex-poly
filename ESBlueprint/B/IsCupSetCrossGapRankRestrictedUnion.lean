import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- Cross-gap A: ending-i left layers restricted by global starting upper rank j, together with starting-j right layers restricted by global ending upper rank i, form a cup. Both potential outer-cup insertions at a mixed cap turn violate a rank bound, contradicting the five-cap-free extension alternative.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq, ErdosSzekeres.isMonochromaticChain_finFive_of_consecutive
@dangling-ok Approved R20 formalization of hand-proved a5 layer compatibility, with an explicit endpoint-extension invariant; coupled polygon deficiency remains open -/
theorem isCupSet_crossGapRankRestrictedUnion {n i j : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (ending starting globalEnding globalStarting : Fin n → ℕ)
    (hi : 2 ≤ i) (hj : 2 ≤ j)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoFive : ¬ContainsCapSet χ (left ∪ right) 5)
    (hnoLeft : ¬ContainsCapSet χ left 4)
    (hnoRight : ¬ContainsCapSet χ right 4)
    (hattainLeft : ∀ x ∈ left, ∃ C : Finset (Fin n), C ⊆ left ∧ C.card = ending x ∧
      IsCupSet χ C ∧ x ∈ C ∧ (∀ y ∈ C, y ≤ x))
    (hmaxLeft : ∀ x ∈ left, ∀ C : Finset (Fin n), C ⊆ left → IsCupSet χ C →
      x ∈ C → (∀ y ∈ C, y ≤ x) → C.card ≤ ending x)
    (hattainRight : ∀ x ∈ right, ∃ C : Finset (Fin n), C ⊆ right ∧ C.card = starting x ∧
      IsCupSet χ C ∧ x ∈ C ∧ (∀ y ∈ C, x ≤ y))
    (hmaxRight : ∀ x ∈ right, ∀ C : Finset (Fin n), C ⊆ right → IsCupSet χ C →
      x ∈ C → (∀ y ∈ C, x ≤ y) → C.card ≤ starting x)
    (hglobalEnd : ∀ x ∈ left ∪ right, ∀ C : Finset (Fin n),
      C ⊆ left ∪ right → IsCupSet χ C → x ∈ C →
        (∀ y ∈ C, y ≤ x) → C.card ≤ globalEnding x)
    (hglobalStart : ∀ x ∈ left ∪ right, ∀ C : Finset (Fin n),
      C ⊆ left ∪ right → IsCupSet χ C → x ∈ C →
        (∀ y ∈ C, x ≤ y) → C.card ≤ globalStarting x) :
    IsCupSet χ ((left.filter (fun x => ending x = i ∧ globalStarting x ≤ j)) ∪
      (right.filter (fun x => starting x = j ∧ globalEnding x ≤ i))) := by
  classical
  have endingLayer {n j : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (rank : Fin n → ℕ)
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
  have startingLayer {n j : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (rank : Fin n → ℕ)
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
  have extensionAlternative {n : ℕ} {χ : TripleColoring n} {s C D : Finset (Fin n)} {a b c : Fin n}
    (hab : a < b) (hbc : b < c) (hone : OneChangeOn χ s)
    (hnoFive : ¬ContainsCapSet χ s 5)
    (hCsub : C ⊆ s) (hDsub : D ⊆ s) (hb : b ∈ s)
    (hCcup : IsCupSet χ C) (hDcup : IsCupSet χ D)
    (haC : a ∈ C) (hcD : c ∈ D)
    (hend : ∀ x ∈ C, x ≤ a) (hstart : ∀ x ∈ D, c ≤ x)
    (hCcard : 2 ≤ C.card) (hDcard : 2 ≤ D.card)
    (hturn : χ ⟨a, b, c, hab, hbc⟩ = Turn.right) :
    IsCupSet χ (insert b C) ∨ IsCupSet χ (insert b D) := by
    classical
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

    by_cases hleft : IsCupSet χ (insert b C)
    · exact Or.inl hleft
    by_cases hright : IsCupSet χ (insert b D)
    · exact Or.inr hright
    apply False.elim
    have hCdrop := Finset.card_erase_add_one haC
    have hCne : (C.erase a).Nonempty := Finset.card_pos.mp (by omega)
    let w := (C.erase a).max' hCne
    have hwErase : w ∈ C.erase a := Finset.max'_mem _ hCne
    obtain ⟨hwNe, hwC⟩ := Finset.mem_erase.mp hwErase
    have hwa : w < a := by
      have hle := hend w hwC
      omega
    have hprev : ∀ x ∈ C, x < a → x ≤ w := by
      intro x hx hxa
      exact Finset.le_max' _ x (Finset.mem_erase.mpr ⟨ne_of_lt hxa, hx⟩)
    have hfirst : χ ⟨w, a, b, hwa, hab⟩ = Turn.right := by
      cases hcol : χ ⟨w, a, b, hwa, hab⟩ with
      | right => rfl
      | left =>
          exact False.elim (hleft (append hCsub hCcup haC hwC hwa hab hb hend hprev hcol))
    have hDdrop := Finset.card_erase_add_one hcD
    have hDne : (D.erase c).Nonempty := Finset.card_pos.mp (by omega)
    let z := (D.erase c).min' hDne
    have hzErase : z ∈ D.erase c := Finset.min'_mem _ hDne
    obtain ⟨hzNe, hzD⟩ := Finset.mem_erase.mp hzErase
    have hcz : c < z := by
      have hle := hstart z hzD
      omega
    have hnext : ∀ x ∈ D, c < x → z ≤ x := by
      intro x hx hcx
      exact Finset.min'_le _ x (Finset.mem_erase.mpr ⟨ne_of_gt hcx, hx⟩)
    have hlast : χ ⟨b, c, z, hbc, hcz⟩ = Turn.right := by
      cases hcol : χ ⟨b, c, z, hbc, hcz⟩ with
      | right => rfl
      | left =>
          exact False.elim (hright (prepend hDsub hDcup hcD hzD hbc hcz hb hstart hnext hcol))
    let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono ![w, a, b, c, z] (by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · simpa using hwa
      · simpa using hab
      · simpa using hbc
      · simpa using hcz)
    have hsub : Finset.univ.image f ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · simpa [f] using hCsub hwC
      · simpa [f] using hCsub haC
      · simpa [f] using hb
      · simpa [f] using hDsub hcD
      · simpa [f] using hDsub hzD
    refine hnoFive ⟨Finset.univ.image f, hsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · exact FinsetPolygon.IsCap.image (isMonochromaticChain_finFive_of_consecutive f
        (hone.mono hsub) (by simpa [f] using hfirst)
        (by simpa [f] using hturn) (by simpa [f] using hlast))
  let A := left.filter (fun x => ending x = i ∧ globalStarting x ≤ j)
  let B := right.filter (fun x => starting x = j ∧ globalEnding x ≤ i)
  have memA {x : Fin n} (hx : x ∈ A) :
      x ∈ left ∧ ending x = i ∧ globalStarting x ≤ j := Finset.mem_filter.mp hx
  have memB {x : Fin n} (hx : x ∈ B) :
      x ∈ right ∧ starting x = j ∧ globalEnding x ≤ i := Finset.mem_filter.mp hx
  have hAglobal : A ⊆ left ∪ right :=
    (Finset.filter_subset _ _).trans Finset.subset_union_left
  have hBglobal : B ⊆ left ∪ right :=
    (Finset.filter_subset _ _).trans Finset.subset_union_right
  have hLeftCup : IsCupSet χ (left.filter (fun x => ending x = i)) :=
    (endingLayer (j := i) ending (hone.mono Finset.subset_union_left)
      hnoLeft hattainLeft hmaxLeft).1
  have hRightCup : IsCupSet χ (right.filter (fun x => starting x = j)) :=
    (startingLayer (j := j) starting (hone.mono Finset.subset_union_right)
      hnoRight hattainRight hmaxRight).1
  have hAcup : IsCupSet χ A := by
    intro t ha hb hc
    exact hLeftCup t (Finset.mem_filter.mpr ⟨(memA ha).1, (memA ha).2.1⟩)
      (Finset.mem_filter.mpr ⟨(memA hb).1, (memA hb).2.1⟩)
      (Finset.mem_filter.mpr ⟨(memA hc).1, (memA hc).2.1⟩)
  have hBcup : IsCupSet χ B := by
    intro t ha hb hc
    exact hRightCup t (Finset.mem_filter.mpr ⟨(memB ha).1, (memB ha).2.1⟩)
      (Finset.mem_filter.mpr ⟨(memB hb).1, (memB hb).2.1⟩)
      (Finset.mem_filter.mpr ⟨(memB hc).1, (memB hc).2.1⟩)
  have mixedCup {a b c : Fin n} (ha : a ∈ A) (hb : b ∈ A ∪ B) (hc : c ∈ B)
      (hab : a < b) (hbc : b < c) :
      χ ⟨a, b, c, hab, hbc⟩ = Turn.left := by
    cases hcol : χ ⟨a, b, c, hab, hbc⟩ with
    | left => rfl
    | right =>
        apply False.elim
        obtain ⟨haL, haRank, _⟩ := memA ha
        obtain ⟨hcR, hcRank, _⟩ := memB hc
        obtain ⟨C, hCsub, hCcard, hCcup, haC, hCend⟩ := hattainLeft a haL
        obtain ⟨D, hDsub, hDcard, hDcup, hcD, hDstart⟩ := hattainRight c hcR
        have hCcardI : C.card = i := hCcard.trans haRank
        have hDcardJ : D.card = j := hDcard.trans hcRank
        have hbS : b ∈ left ∪ right := by
          rcases Finset.mem_union.mp hb with hbA | hbB
          · exact hAglobal hbA
          · exact hBglobal hbB
        have blockedLeft : ¬IsCupSet χ (insert b C) := by
          intro hnew
          have hbNot : b ∉ C := fun hmem => (not_le_of_gt hab) (hCend b hmem)
          have hnewCard : (insert b C).card = i + 1 := by
            rw [Finset.card_insert_of_notMem hbNot, hCcardI]
          have hnewEnd : ∀ z ∈ insert b C, z ≤ b := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact le_rfl
            · exact (hCend z hz).trans hab.le
          rcases Finset.mem_union.mp hb with hbA | hbB
          · obtain ⟨hbL, hbRank, _⟩ := memA hbA
            have hbound := hmaxLeft b hbL (insert b C)
              (Finset.insert_subset_iff.mpr ⟨hbL, hCsub⟩) hnew (by simp) hnewEnd
            rw [hnewCard, hbRank] at hbound
            omega
          · have hbUpper := (memB hbB).2.2
            have hbound := hglobalEnd b hbS (insert b C)
              (Finset.insert_subset_iff.mpr ⟨hbS, hCsub.trans Finset.subset_union_left⟩)
              hnew (by simp) hnewEnd
            rw [hnewCard] at hbound
            omega
        have blockedRight : ¬IsCupSet χ (insert b D) := by
          intro hnew
          have hbNot : b ∉ D := fun hmem => (not_le_of_gt hbc) (hDstart b hmem)
          have hnewCard : (insert b D).card = j + 1 := by
            rw [Finset.card_insert_of_notMem hbNot, hDcardJ]
          have hnewStart : ∀ z ∈ insert b D, b ≤ z := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact le_rfl
            · exact hbc.le.trans (hDstart z hz)
          rcases Finset.mem_union.mp hb with hbA | hbB
          · have hbUpper := (memA hbA).2.2
            have hbound := hglobalStart b hbS (insert b D)
              (Finset.insert_subset_iff.mpr ⟨hbS, hDsub.trans Finset.subset_union_right⟩)
              hnew (by simp) hnewStart
            rw [hnewCard] at hbound
            omega
          · obtain ⟨hbR, hbRank, _⟩ := memB hbB
            have hbound := hmaxRight b hbR (insert b D)
              (Finset.insert_subset_iff.mpr ⟨hbR, hDsub⟩) hnew (by simp) hnewStart
            rw [hnewCard, hbRank] at hbound
            omega
        have hCtwo : 2 ≤ C.card := by omega
        have hDtwo : 2 ≤ D.card := by omega
        rcases extensionAlternative hab hbc hone hnoFive
          (hCsub.trans Finset.subset_union_left) (hDsub.trans Finset.subset_union_right)
          hbS hCcup hDcup haC hcD hCend hDstart hCtwo hDtwo hcol with hnew | hnew
        · exact blockedLeft hnew
        · exact blockedRight hnew
  have leftEarlier {a b : Fin n} (hb : b ∈ A) (hab : a < b)
      (ha : a ∈ A ∪ B) : a ∈ A := by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact ha
    · have hba := horder b (memA hb).1 a (memB ha).1
      omega
  have rightLater {a b : Fin n} (ha : a ∈ B) (hab : a < b)
      (hb : b ∈ A ∪ B) : b ∈ B := by
    rcases Finset.mem_union.mp hb with hb | hb
    · have hba := horder b (memA hb).1 a (memB ha).1
      omega
    · exact hb
  change IsCupSet χ (A ∪ B)
  intro t ha hb hc
  rcases Finset.mem_union.mp hb with hbA | hbB
  · have haA := leftEarlier hbA t.hij ha
    rcases Finset.mem_union.mp hc with hcA | hcB
    · exact hAcup t haA hbA hcA
    · exact mixedCup haA (Finset.mem_union_left B hbA) hcB t.hij t.hjk
  · have hcB := rightLater hbB t.hjk hc
    rcases Finset.mem_union.mp ha with haA | haB
    · exact mixedCup haA (Finset.mem_union_right A hbB) hcB t.hij t.hjk
    · exact hBcup t haB hbB hcB



end ErdosSzekeres
