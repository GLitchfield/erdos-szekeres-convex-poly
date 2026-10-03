import ESBlueprint.B.CtxBoundaryMarkerUpperNormalize

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Exact normalization of a genuine singleton last indexed flank. All children and younger same-axis markers lie strictly on one side, actual labels are positive and its sibling maximum is at least one. Truncate the last maximum and replace its axis parameter by min(global-1,k-maximum): all child-endpoint cup/cap limits, every fuel bound and the full bound are equal. Other-axis markers and unindexed older positive letters are unrestricted. The selected chain count gains exactly one and its join becomes max(oldJoin,oldPure+maximum), explaining the R19 raw PEEL lift.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_boundary_marker_upper_normalize
@dangling-ok Reusable exact effective-parameter invariant verifying the structural explanation of the R19 PEEL counterexample; strengthens the existing one-way boundary normalization -/
theorem ctx_oldest_singleton_flank_normalize (σ : Ctx.Context)
(hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
(N x : ℕ) (hN : N = σ.maxima.length) (hNpos : 1 ≤ N)
(hsingle : σ.extPositions N = [x]) (hmaximum : 1 ≤ σ.maximumAt N)
(rightward : Bool)
(hchildren : ∀ p ∈ σ.childPositions, if rightward then p < x else x < p)
(hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
  if rightward then p < x else x < p) :
let M := σ.maximumAt N
let τ : Ctx.Context := match σ.sideAt N with
  | Ctx.Side.lower => { σ with u := min (σ.u - 1) (σ.k - M), maxima := σ.maxima.take (N - 1) }
  | Ctx.Side.upper => { σ with a := min (σ.a - 1) (σ.k - M), maxima := σ.maxima.take (N - 1) }
(∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
  σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
(∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧
σ.bound = τ.bound := by
  classical
  let norm (ρ : Context) (L : ℕ) : Context := match ρ.sideAt L with
    | Side.lower => { ρ with u := min (ρ.u - 1) (ρ.k - ρ.maximumAt L), maxima := ρ.maxima.take (L - 1) }
    | Side.upper => { ρ with a := min (ρ.a - 1) (ρ.k - ρ.maximumAt L), maxima := ρ.maxima.take (L - 1) }
  change (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, σ.cupLimit p q = (norm σ N).cupLimit p q ∧
      σ.capLimit p q = (norm σ N).capLimit p q) ∧
    (∀ fuel, boundFuel fuel σ = boundFuel fuel (norm σ N)) ∧ σ.bound = (norm σ N).bound
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
  have hPureLeft (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) (p : ℕ) :
      (norm ρ L).leftExt v 0 p = ρ.leftExt v L p := by
    simp only [leftExt_eq, hPureLevels ρ L hL, hLeftStep]
  have hPureRight (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) (p : ℕ) :
      (norm ρ L).rightExt v 0 p = ρ.rightExt v L p := by
    simp only [rightExt_eq, hPureLevels ρ L hL, hRightStep]
  have hLastLevel (ρ : Context) (L : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L) :
      L ∈ ρ.levels := (hLevelMem ρ L).mpr ⟨hL, by omega⟩
  have hFullLevels (ρ : Context) (L : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L) :
      ρ.levels = (norm ρ L).levels ++ [L] := by
    have hs : ((norm ρ L).levels ++ [L]).Pairwise (· < ·) := by
      apply List.pairwise_append.mpr
      refine ⟨hSorted (norm ρ L), by simp, ?_⟩
      intro i hi j hj
      have hjL : j = L := by simpa using hj
      have hiL := (hLevelMem (norm ρ L) i).mp hi
      rw [hMaxima, List.length_take] at hiL
      omega
    apply (hSorted ρ).eq_of_mem_iff hs
    intro j
    simp only [List.mem_append, List.mem_singleton, hLevelMem, hMaxima, List.length_take]
    omega
  have hFullOn (ρ : Context) (L : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (v : Side) : ρ.levelsOn v 0 = (norm ρ L).levelsOn v 0 ++
        (if ρ.sideAt L = v then [L] else []) := by
    unfold levelsOn
    rw [hFullLevels ρ L hLast hL, List.filter_append]
    simp only [hSide, true_or, and_true]
    by_cases hv : ρ.sideAt L = v <;> simp [hv]
  have hBelowOn (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) (top : ℕ)
      (ht : 1 ≤ top) (htL : top ≤ L) : (norm ρ L).levelsOn v top = ρ.levelsOn v top := by
    rw [hLevelsOn]
    apply List.filter_eq_self.mpr
    intro j hj
    have ht' : top = 0 ∨ j < top :=
      (of_decide_eq_true (List.mem_filter.mp hj).2).2
    apply decide_eq_true
    omega
  have hBelowLeft (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) (top p : ℕ)
      (ht : 1 ≤ top) (htL : top ≤ L) :
      (norm ρ L).leftExt v top p = ρ.leftExt v top p := by
    simp only [leftExt_eq, hBelowOn ρ L hL v top ht htL, hLeftStep]
  have hBelowRight (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) (top p : ℕ)
      (ht : 1 ≤ top) (htL : top ≤ L) :
      (norm ρ L).rightExt v top p = ρ.rightExt v top p := by
    simp only [rightExt_eq, hBelowOn ρ L hL v top ht htL, hRightStep]
  have hOtherOn (ρ : Context) (L : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (v : Side) (hv : ρ.sideAt L ≠ v) : ρ.levelsOn v 0 = (norm ρ L).levelsOn v 0 := by
    rw [hFullOn ρ L hLast hL v, if_neg hv, List.append_nil]
  have hOtherChain (ρ : Context) (L : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (v : Side) (hv : ρ.sideAt L ≠ v) (p q : ℕ) :
      ρ.chainExt v p q = (norm ρ L).chainExt v p q := by
    simp only [chainExt, leftExt_eq, rightExt_eq, hOtherOn ρ L hLast hL v hv,
      hLeftStep, hRightStep]
  have hLeftEnd (ρ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
      (ls.foldl (leftStep ρ) z).1 ≤ z.1 := by
    intro ls
    induction ls with
    | nil => intro z; exact le_rfl
    | cons j ls ih =>
      intro z
      have hs : (leftStep ρ z j).1 ≤ z.1 := by
        cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? with
        | none => simp only [leftStep, hh]; exact le_rfl
        | some y =>
          have hy := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
          have hyz : y < z.1 := of_decide_eq_true (List.mem_filter.mp hy).2
          simpa only [leftStep, hh] using hyz.le
      simpa only [List.foldl_cons] using (ih (leftStep ρ z j)).trans hs
  have hRightEnd (ρ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
      z.1 ≤ (ls.foldl (rightStep ρ) z).1 := by
    intro ls
    induction ls with
    | nil => intro z; exact le_rfl
    | cons j ls ih =>
      intro z
      have hs : z.1 ≤ (rightStep ρ z j).1 := by
        cases hh : ((ρ.extPositions j).filter (z.1 < ·)).head? with
        | none => simp only [rightStep, hh]; exact le_rfl
        | some y =>
          have hy := List.mem_of_mem_head? (Option.mem_def.mpr hh)
          have hzy : z.1 < y := of_decide_eq_true (List.mem_filter.mp hy).2
          simpa only [rightStep, hh] using hzy.le
      simpa only [List.foldl_cons] using hs.trans (ih (rightStep ρ z j))
  have hLeftUp (ρ : Context) (L x : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (hSingle : ρ.extPositions L = [x]) (dir : Bool) (p : ℕ)
      (hp : if dir then p < x else x < p) :
      ρ.leftExt (ρ.sideAt L) 0 p ≤ (norm ρ L).leftExt (ρ.sideAt L) 0 p +
        (if dir then 0 else 1) := by
    have hOld (ls : List ℕ) (hls : ls ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists) :
        (ls.foldl (leftStep ρ) (p,0)).2 ≤ (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
      simpa only [leftExt_eq, hLeftStep] using
        (le_getD_max?_of_mem (List.mem_map.mpr ⟨ls,hls,rfl⟩) :
          (ls.foldl (leftStep ρ) (p,0)).2 ≤
            ((((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists.map
              (fun ls => (ls.foldl (leftStep ρ) (p,0)).2)).max?).getD 0)
    have hAppend (ls : List ℕ) :
        ((ls ++ [L]).foldl (leftStep ρ) (p,0)).2 ≤
          (ls.foldl (leftStep ρ) (p,0)).2 + (if dir then 0 else 1) := by
      rw [List.foldl_append]
      change (leftStep ρ (ls.foldl (leftStep ρ) (p,0)) L).2 ≤ _
      cases hd : dir with
      | false =>
        simp only [hd, Bool.false_eq_true, if_false, if_true]
        cases hh : ((ρ.extPositions L).filter
          (· < (ls.foldl (leftStep ρ) (p,0)).1)).getLast? <;> simp [leftStep, hh]
      | true =>
        have he := hLeftEnd ρ ls (p,0)
        have hp' : p < x := by simpa [hd] using hp
        have hn : ¬ x < (ls.foldl (leftStep ρ) (p,0)).1 := by omega
        simp [leftStep, hSingle, hn, hd]
    rw [leftExt_eq, hFullOn ρ L hLast hL, if_pos rfl, List.sublists_concat]
    apply getD_max?_le
    intro y hy
    obtain ⟨ls,hls,rfl⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp hls with hls | hls
    · have h := hOld ls hls
      omega
    · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hls
      exact (hAppend old).trans (Nat.add_le_add_right (hOld old hold) _)
  have hRightUp (ρ : Context) (L x : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (hSingle : ρ.extPositions L = [x]) (dir : Bool) (p : ℕ)
      (hp : if dir then p < x else x < p) :
      ρ.rightExt (ρ.sideAt L) 0 p ≤ (norm ρ L).rightExt (ρ.sideAt L) 0 p +
        (if dir then 1 else 0) := by
    have hOld (ls : List ℕ) (hls : ls ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists) :
        (ls.foldl (rightStep ρ) (p,0)).2 ≤ (norm ρ L).rightExt (ρ.sideAt L) 0 p := by
      simpa only [rightExt_eq, hRightStep] using
        (le_getD_max?_of_mem (List.mem_map.mpr ⟨ls,hls,rfl⟩) :
          (ls.foldl (rightStep ρ) (p,0)).2 ≤
            ((((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists.map
              (fun ls => (ls.foldl (rightStep ρ) (p,0)).2)).max?).getD 0)
    have hAppend (ls : List ℕ) :
        ((ls ++ [L]).foldl (rightStep ρ) (p,0)).2 ≤
          (ls.foldl (rightStep ρ) (p,0)).2 + (if dir then 1 else 0) := by
      rw [List.foldl_append]
      change (rightStep ρ (ls.foldl (rightStep ρ) (p,0)) L).2 ≤ _
      cases hd : dir with
      | true =>
        simp only [hd, if_false, if_true]
        cases hh : ((ρ.extPositions L).filter
          ((ls.foldl (rightStep ρ) (p,0)).1 < ·)).head? <;> simp [rightStep, hh]
      | false =>
        have he := hRightEnd ρ ls (p,0)
        have hp' : x < p := by simpa [hd] using hp
        have hn : ¬ (ls.foldl (rightStep ρ) (p,0)).1 < x := by omega
        simp [rightStep, hSingle, hn, hd]
    rw [rightExt_eq, hFullOn ρ L hLast hL, if_pos rfl, List.sublists_concat]
    apply getD_max?_le
    intro y hy
    obtain ⟨ls,hls,rfl⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp hls with hls | hls
    · have h := hOld ls hls
      omega
    · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hls
      exact (hAppend old).trans (Nat.add_le_add_right (hOld old hold) _)
  have hChainUp (ρ : Context) (L x : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (hSingle : ρ.extPositions L = [x]) (dir : Bool) (p q : ℕ)
      (hp : if dir then p < x else x < p) (hq : if dir then q < x else x < q) :
      ρ.chainExt (ρ.sideAt L) p q ≤ (norm ρ L).chainExt (ρ.sideAt L) p q + 1 := by
    have hl := hLeftUp ρ L x hLast hL hSingle dir p hp
    have hr := hRightUp ρ L x hLast hL hSingle dir q hq
    dsimp only [chainExt]
    cases dir <;> simp only [Bool.false_eq_true, if_false, if_true] at hl hr <;> omega
  have hOtherJoin (ρ : Context) (L : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (v : Side) (hv : ρ.sideAt L ≠ v) (p q : ℕ) :
      ρ.joinExt v p q = (norm ρ L).joinExt v p q := by
    unfold joinExt
    rw [hOtherChain ρ L hLast hL v hv, hOtherOn ρ L hLast hL v hv]
    congr 3
    apply List.map_congr_left
    intro j hj
    have hj1 := (one_le_of_mem_levelsOn hj).1
    have hjL := (hLevelMem (norm ρ L) j).mp (List.mem_filter.mp hj).1
    rw [hMaxima, List.length_take] at hjL
    have hjlt : j < L := by omega
    rw [hBelowLeft ρ L hL v j p hj1 (by omega),
      hBelowRight ρ L hL v j q hj1 (by omega), hMaximum ρ L j hj1 hjlt]
  have hJoinUp (ρ : Context) (L x : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (hSingle : ρ.extPositions L = [x]) (hM : 1 ≤ ρ.maximumAt L) (dir : Bool)
      (p q : ℕ) (hp : if dir then p < x else x < p) (hq : if dir then q < x else x < q) :
      ρ.joinExt (ρ.sideAt L) p q ≤ max ((norm ρ L).joinExt (ρ.sideAt L) p q)
        ((norm ρ L).chainExt (ρ.sideAt L) p q + ρ.maximumAt L) := by
    apply max_le
    · have hc := hChainUp ρ L x hLast hL hSingle dir p q hp hq
      exact le_max_of_le_right (by omega)
    · apply getD_max?_le
      intro t ht
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
      rw [hFullOn ρ L hLast hL, if_pos rfl] at hj
      rcases List.mem_append.mp hj with hj | hj
      · have hj1 := (one_le_of_mem_levelsOn hj).1
        have hjL := (hLevelMem (norm ρ L) j).mp (List.mem_filter.mp hj).1
        rw [hMaxima, List.length_take] at hjL
        have hjlt : j < L := by omega
        rw [← hBelowLeft ρ L hL (ρ.sideAt L) j p hj1 (by omega),
          ← hBelowRight ρ L hL (ρ.sideAt L) j q hj1 (by omega),
          ← hMaximum ρ L j hj1 hjlt]
        exact le_max_of_le_left (le_joinExt_of_mem_levelsOn hj p q)
      · have hjL : j = L := by simpa using hj
        subst j
        rw [← hPureLeft ρ L hL, ← hPureRight ρ L hL]
        exact le_max_right _ _
  have hCaps (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (L x : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (hSingle : ρ.extPositions L = [x]) (hM : 1 ≤ ρ.maximumAt L)
      (dir : Bool) (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      ρ.cupLimit p q = (norm ρ L).cupLimit p q ∧
      ρ.capLimit p q = (norm ρ L).capLimit p q := by
    have hLevel := hLastLevel ρ L hLast hL
    have hx : x ∈ ρ.extPositions L := by rw [hSingle]; simp
    have hUp := (ctx_boundary_marker_upper_normalize ρ hPos L x hLevel hx dir hc hy).1 p hp q hq
    change ρ.cupLimit p q ≤ (norm ρ L).cupLimit p q ∧
      ρ.capLimit p q ≤ (norm ρ L).capLimit p q at hUp
    have hC := hChainUp ρ L x hLast hL hSingle dir p q (hc p hp) (hc q hq)
    have hJ := hJoinUp ρ L x hLast hL hSingle hM dir p q (hc p hp) (hc q hq)
    have hReverse : (norm ρ L).cupLimit p q ≤ ρ.cupLimit p q ∧
        (norm ρ L).capLimit p q ≤ ρ.capLimit p q := by
      cases hs : ρ.sideAt L with
      | lower =>
        have ho : ρ.sideAt L ≠ Side.upper := by simp [hs]
        have hOC := hOtherChain ρ L hLast hL Side.upper ho p q
        have hOJ := hOtherJoin ρ L hLast hL Side.upper ho p q
        rw [hs] at hC hJ
        have ha : (norm ρ L).a = ρ.a := by simp [norm, hs]
        have hu : (norm ρ L).u = min (ρ.u - 1) (ρ.k - ρ.maximumAt L) := by simp [norm, hs]
        dsimp only [cupLimit, capLimit]
        rw [hK, ha, hu, hOC, hOJ]
        omega
      | upper =>
        have ho : ρ.sideAt L ≠ Side.lower := by simp [hs]
        have hOC := hOtherChain ρ L hLast hL Side.lower ho p q
        have hOJ := hOtherJoin ρ L hLast hL Side.lower ho p q
        rw [hs] at hC hJ
        have ha : (norm ρ L).a = min (ρ.a - 1) (ρ.k - ρ.maximumAt L) := by simp [norm, hs]
        have hu : (norm ρ L).u = ρ.u := by simp [norm, hs]
        dsimp only [cupLimit, capLimit]
        rw [hK, ha, hu, hOC, hOJ]
        omega
    exact ⟨Nat.le_antisymm hUp.1 hReverse.1, Nat.le_antisymm hUp.2 hReverse.2⟩
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
  have hBase (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (L x : ℕ) (hLast : L = ρ.maxima.length) (hL : 1 ≤ L)
      (hSingle : ρ.extPositions L = [x]) (hM : 1 ≤ ρ.maximumAt L)
      (dir : Bool) (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p) : ρ.base = (norm ρ L).base := by
    unfold base
    rw [hChild]
    cases hh : ρ.childPositions.head? with
    | none => rfl
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      have h := hCaps ρ hPos L x hLast hL hSingle hM dir hc hy p p hp hp
      simp only [h.1, h.2, hK]
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      ∀ (L x : ℕ), L = ρ.maxima.length → 1 ≤ L →
      ρ.extPositions L = [x] → 1 ≤ ρ.maximumAt L → ∀ dir : Bool,
      (∀ p ∈ ρ.childPositions, if dir then p < x else x < p) →
      (∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p) → boundFuel fuel ρ = boundFuel fuel (norm ρ L) := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro ρ hPos L x hLast hL hSingle hM dir hc hy
      have hLevel := hLastLevel ρ L hLast hL
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) = boundFuel fuel ((norm ρ L).part keep v m) := by
        have hLast' : L+1 = (ρ.part keep v m).maxima.length := by
          simp only [part, List.length_cons]
          omega
        have hSingle' : (ρ.part keep v m).extPositions (L+1) = [x] := by
          rw [part_extPositions_succ ρ keep v m hL]
          exact hSingle
        have hM' : 1 ≤ (ρ.part keep v m).maximumAt (L+1) := by
          rw [part_maximumAt_succ ρ keep v m hL]
          exact hM
        have hNext := hNextBoundary ρ hPos L x hLevel dir hc hy keep v m
        have h := ih (ρ.part keep v m) (hPartPositive ρ keep v m) (L+1) x
          hLast' (by omega) hSingle' hM' dir hNext.1 hNext.2
        rw [hNormPart ρ keep v m L hL] at h
        exact h
      rw [boundFuel.eq_2, boundFuel.eq_2, hRuns]
      by_cases hrun : ρ.numRuns ≤ 1
      · simp only [if_pos hrun]
        exact hBase ρ hPos L x hLast hL hSingle hM dir hc hy
      · simp only [if_neg hrun]
        rw [hBlocks, hChild, hK]
        congr 2
        apply List.flatMap_congr
        intro keep hkeep
        apply List.flatMap_congr
        intro d hd
        rw [hParts, hParts, hParts, hParts]
  refine ⟨fun p hp q hq =>
    hCaps σ hpositive N x hN hNpos hsingle hmaximum rightward hchildren hyounger p q hp hq,
    fun fuel => hFuel fuel σ hpositive N x hN hNpos hsingle hmaximum rightward hchildren hyounger, ?_⟩
  simpa only [bound, hChild] using
    hFuel (σ.childPositions.length+1) σ hpositive N x hN hNpos hsingle hmaximum rightward hchildren hyounger

end ErdosSzekeres
