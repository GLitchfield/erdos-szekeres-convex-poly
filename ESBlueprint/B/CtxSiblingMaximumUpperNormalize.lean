import ESBlueprint.B.CtxPartLimitsLe

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Upper-bound normalization at an indexed sibling level. Absorb its maximum M into the global parameter on its side by capping that parameter at k-M, and truncate the active maxima to the younger prefix before the level. Retain the word and opposite global parameter. Every original cup/cap limit, every fuel approximation and the full recursive bound are at most the corresponding normalized value. Indexed membership alone suffices. This transports large-sibling cases to small-global-axis rank bounds without a run-length restriction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_sibling_maximum_upper_normalize (σ : Ctx.Context) (N : ℕ) (hN : N ∈ σ.levels) :
  let M := σ.maximumAt N
  let τ : Ctx.Context := match σ.sideAt N with
    | Ctx.Side.lower => { σ with u := min σ.u (σ.k - M), maxima := σ.maxima.take (N - 1) }
    | Ctx.Side.upper => { σ with a := min σ.a (σ.k - M), maxima := σ.maxima.take (N - 1) }
  (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧
    σ.bound ≤ τ.bound := by
  classical
  let norm (ρ : Context) (L : ℕ) : Context := match ρ.sideAt L with
    | Side.lower => { ρ with u := min ρ.u (ρ.k - ρ.maximumAt L), maxima := ρ.maxima.take (L - 1) }
    | Side.upper => { ρ with a := min ρ.a (ρ.k - ρ.maximumAt L), maxima := ρ.maxima.take (L - 1) }
  change (∀ p q, σ.cupLimit p q ≤ (norm σ N).cupLimit p q ∧
      σ.capLimit p q ≤ (norm σ N).capLimit p q) ∧
    (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel (norm σ N)) ∧ σ.bound ≤ (norm σ N).bound
  have hWord (ρ : Context) (L : ℕ) : (norm ρ L).word = ρ.word := by
    cases h : ρ.sideAt L <;> simp only [norm, h]
  have hMaxima (ρ : Context) (L : ℕ) : (norm ρ L).maxima = ρ.maxima.take (L - 1) := by
    cases h : ρ.sideAt L <;> simp only [norm, h]
  have hK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := by
    cases h : ρ.sideAt L <;> simp only [norm, h]
  have hLetter (ρ : Context) (L p : ℕ) : (norm ρ L).letterAt p = ρ.letterAt p := by
    simp only [letterAt, hWord]
  have hChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
    simp only [childPositions, hWord, hLetter]
  have hRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
    simp only [numRuns, hWord, hLetter]
  have hBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
    simp only [blocks, hChild]
  have hExt (ρ : Context) (L j : ℕ) : (norm ρ L).extPositions j = ρ.extPositions j := by
    simp only [extPositions, hWord, hLetter]
  have hSide (ρ : Context) (L j : ℕ) : (norm ρ L).sideAt j = ρ.sideAt j := by
    simp only [sideAt, hExt, hLetter]
  have hLeftStep (ρ : Context) (L : ℕ) : leftStep (norm ρ L) = leftStep ρ := by
    funext z j
    simp only [leftStep, hExt]
  have hRightStep (ρ : Context) (L : ℕ) : rightStep (norm ρ L) = rightStep ρ := by
    funext z j
    simp only [rightStep, hExt]
  have hMaximum (ρ : Context) (L j : ℕ) (hj : 1 ≤ j) (hjL : j < L) :
      (norm ρ L).maximumAt j = ρ.maximumAt j := by
    simp only [maximumAt, hMaxima, List.getElem?_take_of_lt (by omega : j - 1 < L - 1)]
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · intro hj
      exact ⟨j - 1, by omega, by omega⟩
  have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
    unfold levels
    exact List.pairwise_lt_range.map (fun x => x + 1) (fun a b hab => Nat.add_lt_add_right hab 1)
  have hLevels (ρ : Context) (L : ℕ) : (norm ρ L).levels = ρ.levels.filter (· < L) := by
    apply (hSorted (norm ρ L)).eq_of_mem_iff ((hSorted ρ).filter _)
    intro j
    simp only [List.mem_filter, hLevelMem, hMaxima, List.length_take, decide_eq_true_eq]
    omega
  have hLevelsOn (ρ : Context) (L : ℕ) (v : Side) (top : ℕ) :
      (norm ρ L).levelsOn v top = (ρ.levelsOn v top).filter (· < L) := by
    simp only [levelsOn, hLevels, hSide, List.filter_filter]
    apply List.filter_congr
    intro j _
    simp only [Bool.and_comm]
  have hSub (ρ : Context) (L : ℕ) (v : Side) (top : ℕ) :
      ((norm ρ L).levelsOn v top).Sublist (ρ.levelsOn v top) := by
    rw [hLevelsOn]
    exact List.filter_sublist
  have hPureLevels (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) :
      (norm ρ L).levelsOn v 0 = ρ.levelsOn v L := by
    rw [hLevelsOn]
    simp only [levelsOn, List.filter_filter]
    apply List.filter_congr
    intro j _
    simp [show L ≠ 0 by omega, Bool.and_comm]
  have hLeftLe (ρ : Context) (L : ℕ) (v : Side) (top p : ℕ) :
      (norm ρ L).leftExt v top p ≤ ρ.leftExt v top p := by
    simp only [leftExt_eq, hLeftStep]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    exact ⟨_, List.mem_map.mpr ⟨ls,
      List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans (hSub ρ L v top)), rfl⟩, le_rfl⟩
  have hRightLe (ρ : Context) (L : ℕ) (v : Side) (top p : ℕ) :
      (norm ρ L).rightExt v top p ≤ ρ.rightExt v top p := by
    simp only [rightExt_eq, hRightStep]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    exact ⟨_, List.mem_map.mpr ⟨ls,
      List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans (hSub ρ L v top)), rfl⟩, le_rfl⟩
  have hPureLeft (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) (p : ℕ) :
      (norm ρ L).leftExt v 0 p = ρ.leftExt v L p := by
    simp only [leftExt_eq, hPureLevels ρ L hL, hLeftStep]
  have hPureRight (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) (p : ℕ) :
      (norm ρ L).rightExt v 0 p = ρ.rightExt v L p := by
    simp only [rightExt_eq, hPureLevels ρ L hL, hRightStep]
  have hChainLe (ρ : Context) (L : ℕ) (v : Side) (p q : ℕ) :
      (norm ρ L).chainExt v p q ≤ ρ.chainExt v p q :=
    Nat.add_le_add (hLeftLe ρ L v 0 p) (hRightLe ρ L v 0 q)
  have hJoinLe (ρ : Context) (L : ℕ) (v : Side) (p q : ℕ) :
      (norm ρ L).joinExt v p q ≤ ρ.joinExt v p q := by
    unfold joinExt
    apply max_le_max (hChainLe ρ L v p q)
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hmem := (hSub ρ L v 0).subset hj
    have hj1 := (one_le_of_mem_levelsOn hmem).1
    have hjL : j < L := by
      rw [hLevelsOn] at hj
      exact of_decide_eq_true (List.mem_filter.mp hj).2
    refine ⟨_, List.mem_map.mpr ⟨j, hmem, rfl⟩, ?_⟩
    rw [hMaximum ρ L j hj1 hjL]
    exact Nat.add_le_add_right (Nat.add_le_add (hLeftLe ρ L v j p) (hRightLe ρ L v j q)) _
  have hCaps (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (p q : ℕ) :
      ρ.cupLimit p q ≤ (norm ρ L).cupLimit p q ∧
      ρ.capLimit p q ≤ (norm ρ L).capLimit p q := by
    have hL1 := one_le_of_mem_levels hL
    have hlevel : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by simp [levelsOn, hL]
    have hJ := le_joinExt_of_mem_levelsOn hlevel p q
    have hcl := hChainLe ρ L Side.lower p q
    have hcu := hChainLe ρ L Side.upper p q
    have hjl := hJoinLe ρ L Side.lower p q
    have hju := hJoinLe ρ L Side.upper p q
    have hpure (v : Side) : (norm ρ L).chainExt v p q = ρ.leftExt v L p + ρ.rightExt v L q := by
      simp only [chainExt, hPureLeft ρ L hL1, hPureRight ρ L hL1]
    cases hs : ρ.sideAt L with
    | lower =>
      have ha : (norm ρ L).a = ρ.a := by simp only [norm, hs]
      have hu : (norm ρ L).u = min ρ.u (ρ.k - ρ.maximumAt L) := by simp only [norm, hs]
      rw [hs] at hJ
      dsimp only [cupLimit, capLimit]
      rw [ha, hu, hK]
      rw [hpure Side.lower] at hcl ⊢
      omega
    | upper =>
      have ha : (norm ρ L).a = min ρ.a (ρ.k - ρ.maximumAt L) := by simp only [norm, hs]
      have hu : (norm ρ L).u = ρ.u := by simp only [norm, hs]
      rw [hs] at hJ
      dsimp only [cupLimit, capLimit]
      rw [ha, hu, hK]
      rw [hpure Side.upper] at hcu ⊢
      omega
  have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL : 1 ≤ L) :
      norm (ρ.part keep v m) (L + 1) = (norm ρ L).part keep v m := by
    have hs := part_sideAt_succ ρ keep v m hL
    have hM := part_maximumAt_succ ρ keep v m hL
    have ht : (m :: ρ.maxima).take (L + 1 - 1) = m :: ρ.maxima.take (L - 1) := by
      rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.take_succ_cons]
    dsimp only [norm]
    rw [hs, hM]
    cases h : ρ.sideAt L <;> simp only [h, part, letterAt, ht]
  have hBase (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) : ρ.base ≤ (norm ρ L).base := by
    rw [base_eq_baseOf, base_eq_baseOf, hChild]
    cases hh : ρ.childPositions.head? with
    | none => exact le_rfl
    | some p =>
      have h := baseOf_mono (k := ρ.k) (hCaps ρ L hL p p).1 (hCaps ρ L hL p p).2
      simpa only [hK] using h
  have hFuel : ∀ fuel (ρ : Context) (L : ℕ), L ∈ ρ.levels →
      boundFuel fuel ρ ≤ boundFuel fuel (norm ρ L) := by
    intro fuel
    induction fuel with
    | zero => intro ρ L _; exact le_rfl
    | succ fuel ih =>
      intro ρ L hL
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel ((norm ρ L).part keep v m) := by
        have hnext : L + 1 ∈ (ρ.part keep v m).levels := by
          rw [part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L, hL, rfl⟩)
        have h := ih (ρ.part keep v m) (L + 1) hnext
        rw [hNormPart ρ keep v m L (one_le_of_mem_levels hL)] at h
        exact h
      simp only [boundFuel, hRuns, hChild, hBlocks, hK]
      split_ifs
      · exact hBase ρ L hL
      · apply Ctx.getD_max?_le_of_forall
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, hkeep, d, hd, hx⟩ := hx
        rcases hx with rfl | rfl
        · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨keep, hkeep, d, hd, Or.inl rfl⟩
        · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨keep, hkeep, d, hd, Or.inr rfl⟩
  refine ⟨fun p q => hCaps σ N hN p q, fun fuel => hFuel fuel σ N hN, ?_⟩
  simpa only [bound, hChild] using hFuel (σ.childPositions.length + 1) σ N hN

end ErdosSzekeres
