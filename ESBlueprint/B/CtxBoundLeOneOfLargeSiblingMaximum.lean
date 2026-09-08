import ESBlueprint.B.CtxPartLimitsLe

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- An indexed sibling maximum at least k-2 bounds every fuel approximation and the full recursive context bound by one. A further split on that level side joins a removed child to the old maximum and annihilates every kept point capacity; the other part retains the large-maximum witness. Positive external labels suffice, with arbitrary child runs, unused levels, maxima and natural k. Supplies an unbounded-length estimate for saturated outer parts at extreme sandwich couplings.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_le_one_of_large_sibling_maximum (σ : Ctx.Context)
  (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
  (N : ℕ) (hN : N ∈ σ.levels)
  (hmaximum : σ.k - 2 ≤ σ.maximumAt N) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 1) ∧ σ.bound ≤ 1 := by
  classical
  let s := σ.sideAt N
  let lim (ρ : Context) (p : ℕ) := match s with
    | Side.lower => ρ.cupLimit p p
    | Side.upper => ρ.capLimit p p
  have hLimPart (ρ : Context) (keep : List ℕ) (t : Side) (m p : ℕ) :
      lim (ρ.part keep t m) p ≤ lim ρ p := by
    have h := ctx_part_limits_le ρ keep t m p p
    cases hs : s with
    | lower => simpa only [lim, hs] using h.1
    | upper => simpa only [lim, hs] using h.2
  have hPositivePart (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ x l u, (ρ.part keep t m).letterAt x = Letter.ext l u → 1 ≤ l := by
    intro x l u hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep t m)
        (show (ρ.part keep t m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep t m hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep t m hxl he] at hx
      cases hx
      omega
  have hLevelPart (ρ : Context) (keep : List ℕ) (t : Side) (m L : ℕ)
      (hL : L ∈ ρ.levelsOn s 0) :
      L + 1 ∈ (ρ.part keep t m).levelsOn s 0 ∧
        (ρ.part keep t m).maximumAt (L + 1) = ρ.maximumAt L := by
    have hmem := (List.mem_filter.mp hL).1
    have h1 := (one_le_of_mem_levelsOn hL).1
    have hside : ρ.sideAt L = s := by simpa using (List.mem_filter.mp hL).2
    have hside' : (ρ.part keep t m).sideAt (L + 1) = s :=
      (part_sideAt_succ ρ keep t m h1).trans hside
    refine ⟨?_, part_maximumAt_succ ρ keep t m h1⟩
    apply List.mem_filter.mpr
    refine ⟨?_, by simp [hside']⟩
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L, hmem, rfl⟩)
  have hUnit (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levelsOn s 0)
      (hM : ρ.k - 2 ≤ ρ.maximumAt L) (p : ℕ) : lim ρ p ≤ 1 := by
    have hj := le_joinExt_of_mem_levelsOn hL p p
    cases hs : s <;> simp only [lim, hs, cupLimit, capLimit] <;>
      simp only [hs] at hj <;> omega
  have hBase (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levelsOn s 0)
      (hM : ρ.k - 2 ≤ ρ.maximumAt L) : ρ.base ≤ 1 := by
    rw [base_eq_baseOf]
    cases hh : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hu := hUnit ρ L hL hM p
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hone : ρ.cupLimit p p = 1 ∨ ρ.capLimit p p = 1 := by
        cases hs : s <;> simp only [lim, hs] at hu <;> omega
      simp [baseOf, hz, hone]
  have hZero : ∀ fuel (ρ : Context),
      (∀ p ∈ ρ.childPositions, lim ρ p = 0) → boundFuel fuel ρ = 0 := by
    intro fuel
    induction fuel with
    | zero => intro ρ _; rfl
    | succ fuel ih =>
      intro ρ hZ
      have hParts (keep : List ℕ) (t : Side) (m : ℕ) : boundFuel fuel (ρ.part keep t m) = 0 := by
        apply ih
        intro p hp
        rw [part_childPositions] at hp
        have hz := hZ p (List.mem_filter.mp hp).1
        have hle := hLimPart ρ keep t m p
        omega
      rw [boundFuel]
      split
      · rw [base_eq_baseOf]
        cases hh : ρ.childPositions.head? with
        | none => rfl
        | some p =>
          have hz := hZ p (List.mem_of_mem_head? (Option.mem_def.mpr hh))
          cases hs : s <;> simp only [lim, hs] at hz <;> simp [baseOf, hz]
      · apply Nat.eq_zero_of_le_zero
        apply Ctx.getD_max?_le
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, _, d, _, hx⟩ := hx
        rcases hx with rfl | rfl <;> simp only [hParts, Nat.add_zero, le_refl]
  have hKill (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (L : ℕ) (hL : L ∈ ρ.levelsOn s 0) (hM : ρ.k - 2 ≤ ρ.maximumAt L)
      (keep : List ℕ) (m r : ℕ) (hr : r ∈ ρ.childPositions) (hremoved : r ∉ keep) :
      ∀ p ∈ (ρ.part keep s m).childPositions, lim (ρ.part keep s m) p = 0 := by
    intro p hp
    let τ := ρ.part keep s m
    have hpkeep : p ∈ keep := by
      rw [part_childPositions] at hp
      simpa using (List.mem_filter.mp hp).2
    have hne : p ≠ r := by intro h; subst p; exact hremoved hpkeep
    have hrnew : r ∈ τ.extPositions 1 := by
      rw [part_extPositions_one hPos keep s m]
      exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
    have hside : τ.sideAt 1 = s := part_sideAt_one_of_mem hPos keep s m hrnew
    have h1 := (one_le_of_mem_levelsOn hL).1
    have hone : 1 ∈ τ.levelsOn s (L + 1) := by
      rw [part_levelsOn_self_succ hside h1]
      simp
    have hsub : [1].Sublist (τ.levelsOn s (L + 1)) := List.singleton_sublist.mpr hone
    have hExt : 1 ≤ τ.leftExt s (L + 1) p + τ.rightExt s (L + 1) p := by
      by_cases hrp : r < p
      · have hnon : ((τ.extPositions 1).filter (· < p)) ≠ [] := by
          intro hn
          have hm : r ∈ (τ.extPositions 1).filter (· < p) :=
            List.mem_filter.mpr ⟨hrnew, by simpa using hrp⟩
          rw [hn] at hm
          cases hm
        have hv := Ctx.le_getD_max?_of_mem
          (L := (τ.levelsOn s (L + 1)).sublists.map
            (fun ls => (ls.foldl (leftStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
        change ([1].foldl (leftStep τ) (p, 0)).2 ≤ τ.leftExt s (L + 1) p at hv
        simp only [List.foldl_cons, List.foldl_nil, leftStep,
          List.getLast?_eq_some_getLast hnon] at hv
        omega
      · have hpr : p < r := by omega
        have hnon : ((τ.extPositions 1).filter (p < ·)) ≠ [] := by
          intro hn
          have hm : r ∈ (τ.extPositions 1).filter (p < ·) :=
            List.mem_filter.mpr ⟨hrnew, by simpa using hpr⟩
          rw [hn] at hm
          cases hm
        have hv := Ctx.le_getD_max?_of_mem
          (L := (τ.levelsOn s (L + 1)).sublists.map
            (fun ls => (ls.foldl (rightStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
        change ([1].foldl (rightStep τ) (p, 0)).2 ≤ τ.rightExt s (L + 1) p at hv
        simp only [List.foldl_cons, List.foldl_nil, rightStep,
          List.head?_eq_some_head hnon] at hv
        omega
    have hlevel := hLevelPart ρ keep s m L hL
    have hj := le_joinExt_of_mem_levelsOn hlevel.1 p p
    rw [hlevel.2] at hj
    have hjoin : ρ.k - 1 ≤ τ.joinExt s p p := by
      change 1 ≤ (ρ.part keep s m).leftExt s (L + 1) p +
        (ρ.part keep s m).rightExt s (L + 1) p at hExt
      change ρ.k - 1 ≤ (ρ.part keep s m).joinExt s p p
      omega
    have hk : τ.k = ρ.k := rfl
    change lim τ p = 0
    cases hs : s <;> simp only [lim, hs, cupLimit, capLimit, hk] <;>
      simp only [hs] at hjoin <;> omega
  have hFuel : ∀ fuel (ρ : Context) (L : ℕ),
      (∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l) →
      L ∈ ρ.levelsOn s 0 → ρ.k - 2 ≤ ρ.maximumAt L → boundFuel fuel ρ ≤ 1 := by
    intro fuel
    induction fuel with
    | zero => intro ρ L _ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ L hPos hL hM
      have hParts (keep : List ℕ) (t : Side) (m : ℕ) : boundFuel fuel (ρ.part keep t m) ≤ 1 := by
        have hlevel := hLevelPart ρ keep t m L hL
        apply ih _ (L + 1) (hPositivePart ρ keep t m) hlevel.1
        rw [hlevel.2]
        exact hM
      have hPair (keep rest : List ℕ) (t : Side) (m n : ℕ)
          (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
          boundFuel fuel (ρ.part keep s m) + boundFuel fuel (ρ.part rest t n) ≤ 1 := by
        by_cases hex : ∃ r, r ∈ (ρ.part rest t n).childPositions
        · obtain ⟨r, hr⟩ := hex
          rw [part_childPositions] at hr
          have hrparent := (List.mem_filter.mp hr).1
          have hrrest : r ∈ rest := by simpa using (List.mem_filter.mp hr).2
          have hnot : r ∉ keep := fun hk => hdis r hrparent hk hrrest
          rw [hZero fuel _ (hKill ρ hPos L hL hM keep m r hrparent hnot), Nat.zero_add]
          exact hParts rest t n
        · have hz : boundFuel fuel (ρ.part rest t n) = 0 := by
            apply hZero
            intro p hp
            exact (hex ⟨p, hp⟩).elim
          rw [hz, Nat.add_zero]
          exact hParts keep s m
      have hPairLR (keep rest : List ℕ) (m n : ℕ)
          (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
          boundFuel fuel (ρ.part keep Side.lower m) +
            boundFuel fuel (ρ.part rest Side.upper n) ≤ 1 := by
        cases hs : s with
        | lower => simpa only [hs] using hPair keep rest Side.upper m n hdis
        | upper =>
          have hrev : ∀ p ∈ ρ.childPositions, p ∈ rest → p ∉ keep := by
            intro p hp hr hk
            exact hdis p hp hk hr
          simpa only [hs, Nat.add_comm] using hPair rest keep Side.lower n m hrev
      rw [boundFuel]
      split
      · exact hBase ρ L hL hM
      · apply Ctx.getD_max?_le
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, _, d, _, hx⟩ := hx
        rcases hx with rfl | rfl
        · apply hPairLR
          intro p _ hp hr
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hr).2
          exact hn hp
        · rw [Nat.add_comm]
          apply hPairLR
          intro p _ hp hk
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hp).2
          exact hn hk
  have hstart : N ∈ σ.levelsOn s 0 := by simp [Context.levelsOn, hN, s]
  have hall : ∀ fuel, boundFuel fuel σ ≤ 1 := fun fuel => hFuel fuel σ N hpositive hstart hmaximum
  exact ⟨hall, hall _⟩

end ErdosSzekeres
