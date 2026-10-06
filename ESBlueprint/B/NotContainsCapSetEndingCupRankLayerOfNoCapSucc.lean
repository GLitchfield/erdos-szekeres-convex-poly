import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- Exact ending-cup rank layers reduce the excluded cap size by one: equal first two ranks force a longest-cup predecessor cap-turn, extending any k-cap to a forbidden (k+1)-cap, uniformly for k≥2.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq
@dangling-ok Approved R20 reusable structural tools for general a≥5; cap-arity reduction explains the layer invariant, coupled polygon deficiency remains open -/
theorem notContainsCapSet_endingCupRankLayer_of_no_cap_succ {n j k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (rank : Fin n → ℕ)
    (hk : 2 ≤ k) (hone : OneChangeOn χ s)
    (hnoCap : ¬ContainsCapSet χ s (k + 1))
    (hattain : ∀ x ∈ s, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = rank x ∧
      IsCupSet χ C ∧ x ∈ C ∧ (∀ y ∈ C, y ≤ x))
    (hmax : ∀ x ∈ s, ∀ C : Finset (Fin n), C ⊆ s → IsCupSet χ C →
      x ∈ C → (∀ y ∈ C, y ≤ x) → C.card ≤ rank x) :
    ¬ContainsCapSet χ (s.filter (fun x => rank x = j)) k := by
  classical
  have cupTwo (a b : Fin n) : IsCupSet χ ({a, b} : Finset (Fin n)) := by
    intro t hi hj hk
    have hij := t.hij
    have hjk := t.hjk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with hi | hi <;> rcases hj with hj | hj <;>
      rcases hk with hk | hk <;> omega

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
  have capPrepend {C : Finset (Fin n)} {y x w : Fin n}
      (hCsub : C ⊆ s) (hcap : IsCapSet χ C) (hx : x ∈ C) (hw : w ∈ C)
      (hyx : y < x) (hxw : x < w) (hy : y ∈ s)
      (hstart : ∀ a ∈ C, x ≤ a) (hnext : ∀ a ∈ C, x < a → w ≤ a)
      (hturn : χ ⟨y, x, w, hyx, hxw⟩ = Turn.right) :
      IsCapSet χ (insert y C) := by
    have endpointTurn (a : Fin n) (ha : a ∈ C) (hxa : x < a) :
        χ ⟨y, x, a, hyx, hxa⟩ = Turn.right := by
      rcases eq_or_lt_of_le (hnext a ha hxa) with rfl | hwa
      · exact hturn
      · have hlast := hcap ⟨x, w, a, hxw, hwa⟩ hx hw ha
        have hseq := hone hyx hxw hwa hy (hCsub hx) (hCsub hw) (hCsub ha)
        have hall := hseq.all_eq_of_outer_eq (hturn.trans hlast.symm)
        exact hall.1.symm.trans hturn
    intro t hi hj hk
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = Turn.right
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
        have hlast := hcap ⟨x, t.j, t.k, hxj, t.hjk⟩ hx hjC hkC
        have hseq := hone hyx hxj t.hjk hy (hCsub hx) (hCsub hjC) (hCsub hkC)
        have hall := hseq.all_eq_of_outer_eq (hfirst.trans hlast.symm)
        simpa [hiy] using hall.2.2.trans hlast
    · have hiC : t.i ∈ C := by simpa [hiy] using hi
      have hyiLt : y < t.i := hyx.trans_le (hstart t.i hiC)
      have hjC : t.j ∈ C := by simpa [ne_of_gt (hyiLt.trans t.hij)] using hj
      have hkC : t.k ∈ C := by
        simpa [ne_of_gt (hyiLt.trans (t.hij.trans t.hjk))] using hk
      exact hcap t hiC hjC hkC
  let A := s.filter (fun x => rank x = j)

  have predecessor {a b : Fin n} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
      ∃ w ∈ s, w < a ∧ CupCap.totalColor χ w a b = Turn.right := by
    obtain ⟨haS, haRank⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbS, hbRank⟩ := Finset.mem_filter.mp hb
    have hpairSub : ({a, b} : Finset (Fin n)) ⊆ s := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact haS
      · exact hbS
    have hpairEnd : ∀ z ∈ ({a, b} : Finset (Fin n)), z ≤ b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hab.le
      · exact le_rfl
    have hpairMax := hmax b hbS {a, b} hpairSub (cupTwo a b) (by simp) hpairEnd
    have hjTwo : 2 ≤ j := by simpa [ne_of_lt hab, hbRank] using hpairMax
    obtain ⟨C, hCsub, hCcard, hCcup, haC, hend⟩ := hattain a haS
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
          have hnewCup := append hCsub hCcup haC hwC
            hwa hab hbS hend hprev hcol
          have hbNot : b ∉ C := fun hmem => (not_le_of_gt hab) (hend b hmem)
          have hnewCard : (insert b C).card = j + 1 := by
            rw [Finset.card_insert_of_notMem hbNot, hCj]
          have hnewSub : insert b C ⊆ s := Finset.insert_subset_iff.mpr ⟨hbS, hCsub⟩
          have hnewEnd : ∀ z ∈ insert b C, z ≤ b := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact le_rfl
            · exact (hend z hz).trans hab.le
          have hnewMax := hmax b hbS (insert b C) hnewSub hnewCup (by simp) hnewEnd
          rw [hnewCard, hbRank] at hnewMax
          omega
    exact ⟨w, hCsub hwC, hwa, (CupCap.totalColor_of_lt χ hwa hab).trans hturn⟩
  change ¬ContainsCapSet χ A k
  rintro ⟨W, hWsub, hWcard, hWcap⟩
  have hWne : W.Nonempty := Finset.card_pos.mp (by omega)
  let a := W.min' hWne
  have haW : a ∈ W := Finset.min'_mem W hWne
  have hmin : ∀ z ∈ W, a ≤ z := fun z hz => Finset.min'_le W z hz
  have hdrop := Finset.card_erase_add_one haW
  have hEraseNe : (W.erase a).Nonempty := Finset.card_pos.mp (by omega)
  let b := (W.erase a).min' hEraseNe
  have hbErase : b ∈ W.erase a := Finset.min'_mem _ hEraseNe
  obtain ⟨hbNe, hbW⟩ := Finset.mem_erase.mp hbErase
  have hab : a < b := by
    have hle := hmin b hbW
    omega
  have hnext : ∀ z ∈ W, a < z → b ≤ z := by
    intro z hz haz
    exact Finset.min'_le _ z (Finset.mem_erase.mpr ⟨ne_of_gt haz, hz⟩)
  obtain ⟨w, hwS, hwa, hturn⟩ := predecessor (hWsub haW) (hWsub hbW) hab
  rw [CupCap.totalColor_of_lt χ hwa hab] at hturn
  have hWsubS : W ⊆ s := hWsub.trans (Finset.filter_subset _ _)
  have hnewCap := capPrepend hWsubS hWcap haW hbW hwa hab hwS hmin hnext hturn
  have hwNot : w ∉ W := by
    intro hwW
    have hle := hmin w hwW
    omega
  have hnewCard : (insert w W).card = k + 1 := by
    rw [Finset.card_insert_of_notMem hwNot, hWcard]
  exact hnoCap ⟨insert w W, Finset.insert_subset_iff.mpr ⟨hwS, hWsubS⟩,
    hnewCard, hnewCap⟩


end ErdosSzekeres
