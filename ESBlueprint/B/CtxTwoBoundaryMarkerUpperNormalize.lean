import ESBlueprint.B.CtxBoundaryMarkerUpperNormalize
import ESBlueprint.B.CtxChainOneStraddlingUniqueAxisLevel

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Absorb two boundary positions of one indexed chosen level as two units of global capacity. When every child and younger same-axis marker lies strictly between those positions, truncating history before the level and capping its axis by min(global-2,k-maximum) can only increase child-endpoint capacities and every recursive fuel/full bound. Both axes, positive labels and unrestricted opposite-axis history are allowed. The proof extends both pure greedy directions to the bracketing level. This isolates the middle-region normalization needed for the next quadratic marker potential.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_boundary_marker_upper_normalize (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x y : ℕ) (hN : N ∈ σ.levels)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions N)
  (hchildren : ∀ p ∈ σ.childPositions, x < p ∧ p < y)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    x < p ∧ p < y) :
  let M := σ.maximumAt N
  let τ : Ctx.Context := match σ.sideAt N with
    | Ctx.Side.lower => { σ with u := min (σ.u - 2) (σ.k - M), maxima := σ.maxima.take (N - 1) }
    | Ctx.Side.upper => { σ with a := min (σ.a - 2) (σ.k - M), maxima := σ.maxima.take (N - 1) }
  (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
    σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧
    σ.bound ≤ τ.bound := by
  classical
  let norm (ρ : Context) (L : ℕ) : Context := match ρ.sideAt L with
    | Side.lower => { ρ with u := min (ρ.u - 2) (ρ.k - ρ.maximumAt L), maxima := ρ.maxima.take (L - 1) }
    | Side.upper => { ρ with a := min (ρ.a - 2) (ρ.k - ρ.maximumAt L), maxima := ρ.maxima.take (L - 1) }
  change (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, σ.cupLimit p q ≤ (norm σ N).cupLimit p q ∧
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
  have hAppend (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side)
      (hLv : L ∈ ρ.levelsOn v 0) (ls : List ℕ) (hls : ls.Sublist (ρ.levelsOn v L)) :
      (ls ++ [L]).Sublist (ρ.levelsOn v 0) := by
    have hL1 := one_le_of_mem_levels hL
    have hy := hSub ρ L v 0
    rw [hPureLevels ρ L hL1 v] at hy
    have hs : (ls ++ [L]).Pairwise (· < ·) := by
      apply List.pairwise_append.mpr
      refine ⟨List.Pairwise.sublist (hls.trans hy) ((hSorted ρ).filter _), by simp, ?_⟩
      intro i hi j hj
      have hjL : j = L := by simpa using hj
      subst j
      have hc : ρ.sideAt i = v ∧ (L = 0 ∨ i < L) :=
        of_decide_eq_true (List.mem_filter.mp (hls.subset hi)).2
      omega
    have hsubset : ls ++ [L] ⊆ ρ.levelsOn v 0 := by
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact (hls.trans hy).subset hj
      · have he : j = L := by simpa using hj
        simpa only [he] using hLv
    have he : (ρ.levelsOn v 0).filter (· ∈ ls ++ [L]) = ls ++ [L] := by
      apply (((hSorted ρ).filter _).filter _).eq_of_mem_iff hs
      intro j
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun hj => ⟨by simpa only [levelsOn, List.mem_filter, decide_eq_true_eq] using hsubset hj, hj⟩⟩
    rw [← he]
    exact List.filter_sublist
  have hEndRight (ρ : Context) (x : ℕ) : ∀ (ls : List ℕ),
      (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, y < x) → ∀ z : ℕ × ℕ,
      z.1 < x → (ls.foldl (rightStep ρ) z).1 < x := by
    intro ls
    induction ls with
    | nil => intro _ z hz; exact hz
    | cons j ls ih =>
      intro hy z hz
      have ht : ∀ i ∈ ls, ∀ y ∈ ρ.extPositions i, y < x :=
        fun i hi y hiy => hy i (by simp [hi]) y hiy
      cases hh : ((ρ.extPositions j).filter (z.1 < ·)).head? with
      | none => simpa only [List.foldl_cons, rightStep, hh] using ih ht z hz
      | some y =>
        have hm := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
        simpa only [List.foldl_cons, rightStep, hh] using ih ht (y,z.2+1) hyx
  have hEndLeft (ρ : Context) (x : ℕ) : ∀ (ls : List ℕ),
      (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, x < y) → ∀ z : ℕ × ℕ,
      x < z.1 → x < (ls.foldl (leftStep ρ) z).1 := by
    intro ls
    induction ls with
    | nil => intro _ z hz; exact hz
    | cons j ls ih =>
      intro hy z hz
      have ht : ∀ i ∈ ls, ∀ y ∈ ρ.extPositions i, x < y :=
        fun i hi y hiy => hy i (by simp [hi]) y hiy
      cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? with
      | none => simpa only [List.foldl_cons, leftStep, hh] using ih ht z hz
      | some y =>
        have hm := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
        have hxy := hy j (by simp) y (List.mem_filter.mp hm).1
        simpa only [List.foldl_cons, leftStep, hh] using ih ht (y,z.2+1) hxy
  have hMoreRight (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side)
      (hLv : L ∈ ρ.levelsOn v 0) (x : ℕ) (hx : x ∈ ρ.extPositions L)
      (hy : ∀ j ∈ ρ.levelsOn v L, ∀ y ∈ ρ.extPositions j, y < x)
      (p : ℕ) (hp : p < x) : (norm ρ L).rightExt v 0 p + 1 ≤ ρ.rightExt v 0 p := by
    have hL1 := one_le_of_mem_levels hL
    have heach (ls : List ℕ) (hls : ls.Sublist (ρ.levelsOn v L)) :
        (ls.foldl (rightStep ρ) (p,0)).2 + 1 ≤ ρ.rightExt v 0 p := by
      let z := ls.foldl (rightStep ρ) (p,0)
      have hz : z.1 < x := hEndRight ρ x ls (fun j hj y hiy => hy j (hls.subset hj) y hiy) (p,0) hp
      have hm : x ∈ (ρ.extPositions L).filter (z.1 < ·) := by simp [hx, hz]
      have hne := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨ls ++ [L], List.mem_sublists.mpr (hAppend ρ L hL v hLv ls hls), rfl⟩)
      change _ ≤ ρ.rightExt v 0 p at hv
      rw [List.foldl_append] at hv
      change (rightStep ρ z L).2 ≤ ρ.rightExt v 0 p at hv
      simpa only [rightStep, List.head?_eq_some_head hne] using hv
    have hOne : 1 ≤ ρ.rightExt v 0 p := by simpa using heach [] (List.nil_sublist _)
    have hb : (norm ρ L).rightExt v 0 p ≤ ρ.rightExt v 0 p - 1 := by
      simp only [rightExt_eq, hPureLevels ρ L hL1 v, hRightStep]
      apply getD_max?_le
      intro c hc
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hc
      have h := heach ls (List.mem_sublists.mp hls)
      simp only [rightExt_eq] at h
      omega
    omega
  have hMoreLeft (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side)
      (hLv : L ∈ ρ.levelsOn v 0) (x : ℕ) (hx : x ∈ ρ.extPositions L)
      (hy : ∀ j ∈ ρ.levelsOn v L, ∀ y ∈ ρ.extPositions j, x < y)
      (p : ℕ) (hp : x < p) : (norm ρ L).leftExt v 0 p + 1 ≤ ρ.leftExt v 0 p := by
    have hL1 := one_le_of_mem_levels hL
    have heach (ls : List ℕ) (hls : ls.Sublist (ρ.levelsOn v L)) :
        (ls.foldl (leftStep ρ) (p,0)).2 + 1 ≤ ρ.leftExt v 0 p := by
      let z := ls.foldl (leftStep ρ) (p,0)
      have hz : x < z.1 := hEndLeft ρ x ls (fun j hj y hiy => hy j (hls.subset hj) y hiy) (p,0) hp
      have hm : x ∈ (ρ.extPositions L).filter (· < z.1) := by simp [hx, hz]
      have hne := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨ls ++ [L], List.mem_sublists.mpr (hAppend ρ L hL v hLv ls hls), rfl⟩)
      change _ ≤ ρ.leftExt v 0 p at hv
      rw [List.foldl_append] at hv
      change (leftStep ρ z L).2 ≤ ρ.leftExt v 0 p at hv
      simpa only [leftStep, List.getLast?_eq_some_getLast hne] using hv
    have hOne : 1 ≤ ρ.leftExt v 0 p := by simpa using heach [] (List.nil_sublist _)
    have hb : (norm ρ L).leftExt v 0 p ≤ ρ.leftExt v 0 p - 1 := by
      simp only [leftExt_eq, hPureLevels ρ L hL1 v, hLeftStep]
      apply getD_max?_le
      intro c hc
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hc
      have h := heach ls (List.mem_sublists.mp hls)
      simp only [leftExt_eq] at h
      omega
    omega
  have hCaps (ρ : Context) (L x y : ℕ) (hL : L ∈ ρ.levels)
      (hx : x ∈ ρ.extPositions L) (hy : y ∈ ρ.extPositions L)
      (hc : ∀ p ∈ ρ.childPositions, x < p ∧ p < y)
      (hyng : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        x < p ∧ p < y)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      ρ.cupLimit p q ≤ (norm ρ L).cupLimit p q ∧
      ρ.capLimit p q ≤ (norm ρ L).capLimit p q := by
    have hL1 := one_le_of_mem_levels hL
    have hlevel : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by simp [levelsOn, hL]
    have hplus : (norm ρ L).chainExt (ρ.sideAt L) p q + 2 ≤ ρ.chainExt (ρ.sideAt L) p q := by
      have hl := hMoreLeft ρ L hL (ρ.sideAt L) hlevel x hx
        (fun j hj z hjz => (hyng j hj z hjz).1) p (hc p hp).1
      have hr := hMoreRight ρ L hL (ρ.sideAt L) hlevel y hy
        (fun j hj z hjz => (hyng j hj z hjz).2) q (hc q hq).2
      dsimp only [chainExt]
      omega
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
      have hu : (norm ρ L).u = min (ρ.u-2) (ρ.k - ρ.maximumAt L) := by simp only [norm, hs]
      rw [hs] at hJ hplus
      dsimp only [cupLimit, capLimit]
      rw [ha, hu, hK]
      rw [hpure Side.lower] at hcl hplus ⊢
      omega
    | upper =>
      have ha : (norm ρ L).a = min (ρ.a-2) (ρ.k - ρ.maximumAt L) := by simp only [norm, hs]
      have hu : (norm ρ L).u = ρ.u := by simp only [norm, hs]
      rw [hs] at hJ hplus
      dsimp only [cupLimit, capLimit]
      rw [ha, hu, hK]
      rw [hpure Side.upper] at hcu hplus ⊢
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
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ x j w, (ρ.part keep v m).letterAt x = Letter.ext j w → 1 ≤ j := by
    intro x j w hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep v m)
        (show (ρ.part keep v m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep v m hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep v m hxl he] at hx
      cases hx
      omega
  have hNextBoundary (ρ : Context)
      (hPos : ∀ p j w, ρ.letterAt p = Letter.ext j w → 1 ≤ j)
      (L x : ℕ) (hL : L ∈ ρ.levels) (dir : Bool)
      (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (keep : List ℕ) (v : Side) (m : ℕ) :
      (∀ p ∈ (ρ.part keep v m).childPositions, if dir then p < x else x < p) ∧
      (∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) (L+1),
        ∀ p ∈ (ρ.part keep v m).extPositions j, if dir then p < x else x < p) := by
    have hL1 := one_le_of_mem_levels hL
    constructor
    · intro p hp
      rw [part_childPositions] at hp
      exact hc p (List.mem_filter.mp hp).1
    · intro j hj p hp
      have hj1 := (one_le_of_mem_levelsOn hj).1
      by_cases he : j = 1
      · subst j
        rw [part_extPositions_one hPos keep v m] at hp
        exact hc p (List.mem_filter.mp hp).1
      · let i := j-1
        have hi : 1 ≤ i := by dsimp [i]; omega
        have he : j = i+1 := by dsimp [i]; omega
        rw [he] at hj hp
        have hjLevel : i+1 ∈ (ρ.part keep v m).levels := (List.mem_filter.mp hj).1
        rw [part_levels] at hjLevel
        have hiLevel : i ∈ ρ.levels := by
          rcases List.mem_cons.mp hjLevel with h | h
          · omega
          · obtain ⟨z, hz, hzi⟩ := List.mem_map.mp h
            have hz' : z = i := by omega
            simpa only [hz'] using hz
        have hjc : (ρ.part keep v m).sideAt (i+1) = (ρ.part keep v m).sideAt (L+1) ∧
            (L+1 = 0 ∨ i+1 < L+1) := of_decide_eq_true (List.mem_filter.mp hj).2
        rw [part_sideAt_succ ρ keep v m hi, part_sideAt_succ ρ keep v m hL1] at hjc
        have hiOn : i ∈ ρ.levelsOn (ρ.sideAt L) L := by
          apply List.mem_filter.mpr
          refine ⟨hiLevel, ?_⟩
          apply decide_eq_true
          exact ⟨hjc.1, Or.inr (by omega)⟩
        rw [part_extPositions_succ ρ keep v m hi] at hp
        exact hy i hiOn p hp
  have hBase (ρ : Context) (L x y : ℕ) (hL : L ∈ ρ.levels)
      (hx : x ∈ ρ.extPositions L) (hy : y ∈ ρ.extPositions L)
      (hc : ∀ p ∈ ρ.childPositions, x < p ∧ p < y)
      (hyng : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        x < p ∧ p < y) : ρ.base ≤ (norm ρ L).base := by
    rw [base_eq_baseOf, base_eq_baseOf, hChild]
    cases hh : ρ.childPositions.head? with
    | none => exact le_rfl
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      have h := hCaps ρ L x y hL hx hy hc hyng p p hp hp
      simpa only [hK] using baseOf_mono (k := ρ.k) h.1 h.2
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      ∀ (L x y : ℕ), L ∈ ρ.levels → x ∈ ρ.extPositions L → y ∈ ρ.extPositions L →
      (∀ p ∈ ρ.childPositions, x < p ∧ p < y) →
      (∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        x < p ∧ p < y) → boundFuel fuel ρ ≤ boundFuel fuel (norm ρ L) := by
    intro fuel
    induction fuel with
    | zero => intro ρ hPos L x y hL hx hy hc hyng; exact le_rfl
    | succ fuel ih =>
      intro ρ hPos L x y hL hx hy hc hyng
      have hL1 := one_le_of_mem_levels hL
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel ((norm ρ L).part keep v m) := by
        have hn : L+1 ∈ (ρ.part keep v m).levels := by
          rw [part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L,hL,rfl⟩)
        have hx' : x ∈ (ρ.part keep v m).extPositions (L+1) := by
          rw [part_extPositions_succ ρ keep v m hL1]
          exact hx
        have hy' : y ∈ (ρ.part keep v m).extPositions (L+1) := by
          rw [part_extPositions_succ ρ keep v m hL1]
          exact hy
        have hl := hNextBoundary ρ hPos L x hL false
          (fun p hp => (hc p hp).1) (fun j hj p hp => (hyng j hj p hp).1) keep v m
        have hr := hNextBoundary ρ hPos L y hL true
          (fun p hp => (hc p hp).2) (fun j hj p hp => (hyng j hj p hp).2) keep v m
        have h := ih (ρ.part keep v m) (hPartPositive ρ keep v m) (L+1) x y hn hx' hy'
          (fun p hp => ⟨hl.1 p hp, hr.1 p hp⟩)
          (fun j hj p hp => ⟨hl.2 j hj p hp, hr.2 j hj p hp⟩)
        rw [hNormPart ρ keep v m L hL1] at h
        exact h
      simp only [boundFuel, hRuns, hChild, hBlocks, hK]
      split_ifs
      · exact hBase ρ L x y hL hx hy hc hyng
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
  refine ⟨fun p hp q hq => hCaps σ N x y hN hx hy hchildren hyounger p q hp hq,
    fun fuel => hFuel fuel σ hpositive N x y hN hx hy hchildren hyounger, ?_⟩
  simpa only [bound, hChild] using
    hFuel (σ.childPositions.length+1) σ hpositive N x y hN hx hy hchildren hyounger

end ErdosSzekeres
