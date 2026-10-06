import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- Strengthened cross-gap B: an exact ending-rank cup layer on a four-cap-free side joined to any ordered later cup has no four-cap under ambient OneChange and no five-cap. A hypothetical2|2 four-cap extends by a longest-cup predecessor to a five-cap.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq, ErdosSzekeres.isMonochromaticChain_finFive_of_consecutive
@dangling-ok Approved R20 structural a5 tool permitting the proved uniform diagonal bound on layer/cup unions; right starting ranks are unnecessary, coupled cut remains open -/
theorem notContainsCapFour_endingCupLayer_union_laterCup {n j : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)} (rank : Fin n → ℕ)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoLeft : ¬ContainsCapSet χ left 4)
    (hnoFive : ¬ContainsCapSet χ (left ∪ right) 5)
    (hright : IsCupSet χ right)
    (hattain : ∀ x ∈ left, ∃ C : Finset (Fin n), C ⊆ left ∧ C.card = rank x ∧
      IsCupSet χ C ∧ x ∈ C ∧ (∀ y ∈ C, y ≤ x))
    (hmax : ∀ x ∈ left, ∀ C : Finset (Fin n), C ⊆ left → IsCupSet χ C →
      x ∈ C → (∀ y ∈ C, y ≤ x) → C.card ≤ rank x) :
    ¬ContainsCapSet χ ((left.filter (fun x => rank x = j)) ∪ right) 4 := by
  classical
  let s := left ∪ right
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
  have cupTwo (a b : Fin n) : IsCupSet χ ({a, b} : Finset (Fin n)) := by
    intro t hi hj hk
    have hij := t.hij
    have hjk := t.hjk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with hi | hi <;> rcases hj with hj | hj <;>
      rcases hk with hk | hk <;> omega
  let A := left.filter (fun x => rank x = j)
  have hALeft : A ⊆ left := Finset.filter_subset _ _
  have hAcup : IsCupSet χ A :=
    (endingLayer (j := j) rank (hone.mono Finset.subset_union_left) hnoLeft hattain hmax).1
  have predecessor {a b : Fin n} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
      ∃ w ∈ left, w < a ∧ CupCap.totalColor χ w a b = Turn.right := by
    obtain ⟨haL, haRank⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbL, hbRank⟩ := Finset.mem_filter.mp hb
    have hpairSub : ({a, b} : Finset (Fin n)) ⊆ left := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact haL
      · exact hbL
    have hpairEnd : ∀ z ∈ ({a, b} : Finset (Fin n)), z ≤ b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hab.le
      · exact le_rfl
    have hpairMax := hmax b hbL {a, b} hpairSub (cupTwo a b) (by simp) hpairEnd
    have hjTwo : 2 ≤ j := by simpa [ne_of_lt hab, hbRank] using hpairMax
    obtain ⟨C, hCsub, hCcard, hCcup, haC, hend⟩ := hattain a haL
    have hCj : C.card = j := hCcard.trans haRank
    have hErase := Finset.card_erase_add_one haC
    have hne : (C.erase a).Nonempty := Finset.card_pos.mp (by omega)
    let w := (C.erase a).max' hne
    have hwErase : w ∈ C.erase a := Finset.max'_mem _ hne
    obtain ⟨hwNe, hwC⟩ := Finset.mem_erase.mp hwErase
    have hwa : w < a := by
      have hwLe := hend w hwC
      omega
    have hprev : ∀ z ∈ C, z < a → z ≤ w := by
      intro z hz hza
      exact Finset.le_max' _ z (Finset.mem_erase.mpr ⟨ne_of_lt hza, hz⟩)
    have hturn : χ ⟨w, a, b, hwa, hab⟩ = Turn.right := by
      cases hcol : χ ⟨w, a, b, hwa, hab⟩ with
      | right => rfl
      | left =>
          apply False.elim
          have hnewCup := append (hCsub.trans Finset.subset_union_left) hCcup haC hwC
            hwa hab (Finset.mem_union_left right hbL) hend hprev hcol
          have hbNot : b ∉ C := fun hmem => (not_le_of_gt hab) (hend b hmem)
          have hnewCard : (insert b C).card = j + 1 := by
            rw [Finset.card_insert_of_notMem hbNot, hCj]
          have hnewSub : insert b C ⊆ left := Finset.insert_subset_iff.mpr ⟨hbL, hCsub⟩
          have hnewEnd : ∀ z ∈ insert b C, z ≤ b := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact le_rfl
            · exact (hend z hz).trans hab.le
          have hnewMax := hmax b hbL (insert b C) hnewSub hnewCup (by simp) hnewEnd
          rw [hnewCard, hbRank] at hnewMax
          omega
    exact ⟨w, hCsub hwC, hwa, (CupCap.totalColor_of_lt χ hwa hab).trans hturn⟩
  change ¬ContainsCapSet χ (A ∪ right) 4
  rintro ⟨W, hWsub, hWcard, hWcap⟩
  let f : Fin 4 ↪o Fin n := W.orderEmbOfFin hWcard
  have hfmem (i : Fin 4) : f i ∈ W := Finset.orderEmbOfFin_mem W hWcard i
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h12 : f 1 < f 2 := f.strictMono (by decide)
  have h23 : f 2 < f 3 := f.strictMono (by decide)
  have h0 := hWsub (hfmem 0)
  have h1 := hWsub (hfmem 1)
  have h2 := hWsub (hfmem 2)
  have h3 := hWsub (hfmem 3)
  have h012 := hWcap ⟨f 0, f 1, f 2, h01, h12⟩ (hfmem 0) (hfmem 1) (hfmem 2)
  have h123 := hWcap ⟨f 1, f 2, f 3, h12, h23⟩ (hfmem 1) (hfmem 2) (hfmem 3)
  have rightLater {a b : Fin n} (ha : a ∈ right) (hab : a < b)
      (hb : b ∈ A ∪ right) : b ∈ right := by
    rcases Finset.mem_union.mp hb with hb | hb
    · have hba := horder b (hALeft hb) a ha
      omega
    · exact hb
  have leftEarlier {a b : Fin n} (hb : b ∈ A) (hab : a < b)
      (ha : a ∈ A ∪ right) : a ∈ A := by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact ha
    · have hba := horder b (hALeft hb) a ha
      omega
  have h1A : f 1 ∈ A := by
    rcases Finset.mem_union.mp h1 with hA | hR
    · exact hA
    · have h2R := rightLater hR h12 h2
      have h3R := rightLater h2R h23 h3
      have hcup := hright ⟨f 1, f 2, f 3, h12, h23⟩ hR h2R h3R
      have hbad := hcup.symm.trans h123
      cases hbad
  have h0A : f 0 ∈ A := leftEarlier h1A h01 h0
  have h2R : f 2 ∈ right := by
    rcases Finset.mem_union.mp h2 with hA | hR
    · have hcup := hAcup ⟨f 0, f 1, f 2, h01, h12⟩ h0A h1A hA
      have hbad := hcup.symm.trans h012
      cases hbad
    · exact hR
  have h3R : f 3 ∈ right := rightLater h2R h23 h3
  obtain ⟨w, hwL, hw0, hturn⟩ := predecessor h0A h1A h01
  rw [CupCap.totalColor_of_lt χ hw0 h01] at hturn
  let g : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono ![w, f 0, f 1, f 2, f 3] (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · simpa using hw0
    · simpa using h01
    · simpa using h12
    · simpa using h23)
  have hAsub : A ∪ right ⊆ s := Finset.union_subset_union hALeft (Finset.Subset.refl _)
  have hsub : Finset.univ.image g ⊆ s := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨i, rfl⟩ := hz
    fin_cases i
    · simpa [g, s] using Finset.mem_union_left right hwL
    · simpa [g] using hAsub h0
    · simpa [g] using hAsub h1
    · simpa [g] using hAsub h2
    · simpa [g] using hAsub h3
  apply hnoFive
  refine ⟨Finset.univ.image g, hsub, ?_, ?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ g.injective
  · exact FinsetPolygon.IsCap.image (isMonochromaticChain_finFive_of_consecutive g
      (hone.mono hsub) (by simpa [g] using hturn)
      (by simpa [g] using h012) (by simpa [g] using h123))


end ErdosSzekeres
