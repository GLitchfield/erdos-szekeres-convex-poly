import ESBlueprint.B.CtxBoundaryMarkerEraseNormalize

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Erase a sole indexed boundary marker and absorb its positive maximum into the selected global capacity. Under positive labels, children and younger same-axis markers strictly on one side of that marker, and no older marker on its axis, the existing boundary-erasure normalization preserves every child-endpoint limit and every recursive fuel/full bound exactly. Retains all opposite-axis history. Supplies exact complement normalization for the exposed-end route to the four-end singleton selector.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_boundary_marker_erase_normalize
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_boundary_singleton_marker_erase_normalize_exact (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (N x : ℕ) (hN : N ∈ σ.levels)
    (hsole : σ.extPositions N = [x])
    (hmaximum : 1 ≤ σ.maximumAt N)
    (rightward : Bool)
    (hchildren : ∀ p ∈ σ.childPositions, if rightward then p < x else x < p)
    (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
      if rightward then p < x else x < p)
    (hterminal : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, j ≤ N) :
  let ρ : Ctx.Context := { σ with
    word := σ.word.map (fun z => match z with
      | Ctx.Letter.child => Ctx.Letter.child
      | Ctx.Letter.ext j v => Ctx.Letter.ext
          (if j = N then σ.maxima.length else if N < j then j - 1 else j) v)
    maxima := σ.maxima.eraseIdx (N - 1) }
  let τ : Ctx.Context := match σ.sideAt N with
    | Ctx.Side.lower => { ρ with u := min (σ.u - 1) (σ.k - σ.maximumAt N) }
    | Ctx.Side.upper => { ρ with a := min (σ.a - 1) (σ.k - σ.maximumAt N) }
  (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
    σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
  (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧
  σ.bound = τ.bound := by
  classical
  let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
  let letter (D L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext (idx D L j) v
  let erase (ρ : Context) (L : ℕ) : Context :=
    { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L-1) }
  let up (L j : ℕ) := if j < L then j else j+1
  let norm (ρ : Context) (L : ℕ) : Context := match ρ.sideAt L with
    | Side.lower => { erase ρ L with u := min (ρ.u-1) (ρ.k-ρ.maximumAt L) }
    | Side.upper => { erase ρ L with a := min (ρ.a-1) (ρ.k-ρ.maximumAt L) }
  let trunc (ρ : Context) (L : ℕ) : Context := match ρ.sideAt L with
    | Side.lower => { ρ with u := min (ρ.u-1) (ρ.k-ρ.maximumAt L), maxima := ρ.maxima.take (L-1) }
    | Side.upper => { ρ with a := min (ρ.a-1) (ρ.k-ρ.maximumAt L), maxima := ρ.maxima.take (L-1) }
  change (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
    σ.cupLimit p q = (norm σ N).cupLimit p q ∧ σ.capLimit p q = (norm σ N).capLimit p q) ∧
    (∀ fuel, boundFuel fuel σ = boundFuel fuel (norm σ N)) ∧ σ.bound = (norm σ N).bound
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro hj; exact ⟨j-1, by omega, by omega⟩
  have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
    unfold levels
    exact List.pairwise_lt_range.map (fun x => x+1) (fun a b h => Nat.add_lt_add_right h 1)
  have hLen (ρ : Context) (L : ℕ) : (erase ρ L).word.length = ρ.word.length := by
    simp only [erase, List.length_map]
  have hLetter (ρ : Context) (L p : ℕ) :
      (erase ρ L).letterAt p = letter ρ.maxima.length L (ρ.letterAt p) := by
    simp only [erase, letterAt, List.getElem?_map]
    cases ρ.word[p]? <;> rfl
  have hIsChild (ρ : Context) (L p : ℕ) :
      (erase ρ L).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
    rw [hLetter]
    cases ρ.letterAt p <;> simp [letter]
  have hChild (ρ : Context) (L : ℕ) : (erase ρ L).childPositions = ρ.childPositions := by
    simp only [childPositions, hLen, hIsChild]
  have hRuns (ρ : Context) (L : ℕ) : (erase ρ L).numRuns = ρ.numRuns := by
    simp only [numRuns, hLen, ne_eq, hIsChild]
  have hBlocks (ρ : Context) (L : ℕ) : (erase ρ L).blocks = ρ.blocks := by
    simp only [blocks, hChild]
  have hK (ρ : Context) (L : ℕ) : (erase ρ L).k = ρ.k := rfl
  have hDepth (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      (erase ρ L).maxima.length = ρ.maxima.length-1 := by
    have hh := (hLevelMem ρ L).mp hL
    exact List.length_eraseIdx_of_lt (by omega)
  have hLive (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (erase ρ L).levels) :
      1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
    have hh := (hLevelMem ρ L).mp hL
    have hj' := (hLevelMem (erase ρ L) j).mp hj
    rw [hDepth ρ L hL] at hj'
    refine ⟨hj'.1, by omega, ?_⟩
    apply (hLevelMem ρ _).mpr
    dsimp [up]
    split_ifs <;> omega
  have hIndex (D L i j : ℕ) (hL : 1 ≤ L) (hLD : L ≤ D)
      (hj : 1 ≤ j) (hjD : j < D) : idx D L i = j ↔ i = up L j := by
    dsimp [idx, up]
    split_ifs <;> omega
  have hExt (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (erase ρ L).levels) :
      (erase ρ L).extPositions j = ρ.extPositions (up L j) := by
    have hLj := (hLevelMem ρ L).mp hL
    have hj' := hLive ρ L j hL hj
    simp only [extPositions, hLen, hLetter]
    apply List.filter_congr
    intro p _
    cases ρ.letterAt p with
    | child => rfl
    | ext i v => simp only [letter, hIndex _ _ i j hLj.1 hLj.2 hj'.1 hj'.2.1]
  have hSide (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (erase ρ L).levels) : (erase ρ L).sideAt j = ρ.sideAt (up L j) := by
    simp only [sideAt, hExt ρ L j hL hj]
    cases hh : (ρ.extPositions (up L j)).head? with
    | none => rfl
    | some p =>
      dsimp only
      rw [hLetter]
      cases ρ.letterAt p <;> rfl
  have hMaximum (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (erase ρ L).levels) : (erase ρ L).maximumAt j = ρ.maximumAt (up L j) := by
    have hh := (hLevelMem ρ L).mp hL
    have hj' := (hLive ρ L j hL hj).1
    simp only [maximumAt, erase, List.getElem?_eraseIdx]
    by_cases h : j < L
    · simp [up, h, show j-1 < L-1 by omega]
    · simp [up, h, show ¬j-1 < L-1 by omega, show j-1+1 = j by omega]
  have hNormChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
    cases hs : ρ.sideAt L <;> simpa only [norm, hs] using hChild ρ L
  have hNormRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
    cases hs : ρ.sideAt L <;> simpa only [norm, hs] using hRuns ρ L
  have hNormBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
    simp only [blocks, hNormChild]
  have hNormK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := by
    cases hs : ρ.sideAt L <;> simp only [norm, hs] <;> rfl
  have hTruncMax (ρ : Context) (L : ℕ) : (trunc ρ L).maxima = ρ.maxima.take (L-1) := by
    cases hs : ρ.sideAt L <;> simp only [trunc, hs]
  have hTruncExt (ρ : Context) (L j : ℕ) : (trunc ρ L).extPositions j = ρ.extPositions j := by
    cases hs : ρ.sideAt L <;> simp only [trunc, hs] <;> rfl
  have hTruncSide (ρ : Context) (L j : ℕ) : (trunc ρ L).sideAt j = ρ.sideAt j := by
    cases hs : ρ.sideAt L <;> simp only [trunc, hs] <;> rfl
  have hOwnYoung (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L)
      (top j : ℕ) (hj : j ∈ (erase ρ L).levelsOn (ρ.sideAt L) top) : j < L := by
    have hjl := (List.mem_filter.mp hj).1
    have hside : (erase ρ L).sideAt j = ρ.sideAt L :=
      (of_decide_eq_true (List.mem_filter.mp hj).2).1
    rw [hSide ρ L j hL hjl] at hside
    have hm : up L j ∈ ρ.levelsOn (ρ.sideAt L) 0 :=
      List.mem_filter.mpr ⟨(hLive ρ L j hL hjl).2.2, by simp [hside]⟩
    have hh := ht _ hm
    dsimp only [up] at hh
    split_ifs at hh <;> omega
  have hOwnLevels (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) (top : ℕ) :
      (erase ρ L).levelsOn (ρ.sideAt L) top = (trunc ρ L).levelsOn (ρ.sideAt L) top := by
    apply ((hSorted (erase ρ L)).filter _).eq_of_mem_iff ((hSorted (trunc ρ L)).filter _)
    intro j
    constructor
    · intro hj
      have hjl := (List.mem_filter.mp hj).1
      have hjc : (erase ρ L).sideAt j = ρ.sideAt L ∧ (top = 0 ∨ j < top) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      have hjL := hOwnYoung ρ L hL ht top j hj
      have hj1 := (hLive ρ L j hL hjl).1
      have hLD := ((hLevelMem ρ L).mp hL).2
      have hup : up L j = j := by simp [up, hjL]
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply (hLevelMem (trunc ρ L) j).mpr
        rw [hTruncMax, List.length_take]
        omega
      · apply decide_eq_true
        rw [hSide ρ L j hL hjl, hup] at hjc
        rw [hTruncSide]
        exact hjc
    · intro hj
      have hjl := (hLevelMem (trunc ρ L) j).mp (List.mem_filter.mp hj).1
      rw [hTruncMax, List.length_take] at hjl
      have hL1 := one_le_of_mem_levels hL
      have hjL : j < L := by omega
      have hLD := ((hLevelMem ρ L).mp hL).2
      have hje : j ∈ (erase ρ L).levels := by
        apply (hLevelMem (erase ρ L) j).mpr
        rw [hDepth ρ L hL]
        omega
      have hjc : (trunc ρ L).sideAt j = ρ.sideAt L ∧ (top = 0 ∨ j < top) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      rw [hTruncSide] at hjc
      apply List.mem_filter.mpr
      refine ⟨hje, ?_⟩
      apply decide_eq_true
      rw [hSide ρ L j hL hje, show up L j = j by simp [up, hjL]]
      exact hjc
  have hOwnExt (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L)
      (top j : ℕ) (hj : j ∈ (erase ρ L).levelsOn (ρ.sideAt L) top) :
      (erase ρ L).extPositions j = (trunc ρ L).extPositions j := by
    rw [hExt ρ L j hL (List.mem_filter.mp hj).1, hTruncExt]
    rw [show up L j = j by simp [up, hOwnYoung ρ L hL ht top j hj]]
  have hOwnMaximum (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L)
      (top j : ℕ) (hj : j ∈ (erase ρ L).levelsOn (ρ.sideAt L) top) :
      (erase ρ L).maximumAt j = (trunc ρ L).maximumAt j := by
    have hjL := hOwnYoung ρ L hL ht top j hj
    have hj1 := (one_le_of_mem_levelsOn hj).1
    rw [hMaximum ρ L j hL (List.mem_filter.mp hj).1,
      show up L j = j by simp [up, hjL]]
    simp only [maximumAt, hTruncMax, List.getElem?_take_of_lt (by omega : j-1 < L-1)]
  have hOwnLeft (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) (top p : ℕ) :
      (erase ρ L).leftExt (ρ.sideAt L) top p = (trunc ρ L).leftExt (ρ.sideAt L) top p := by
    have hf : ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase ρ L).levelsOn (ρ.sideAt L) top) →
        ∀ z, ls.foldl (leftStep (erase ρ L)) z = ls.foldl (leftStep (trunc ρ L)) z := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hj z
        simp only [List.foldl_cons, leftStep, hOwnExt ρ L hL ht top j (hj j (by simp))]
        exact ih (fun i hi => hj i (by simp [hi])) _
    rw [leftExt_eq, leftExt_eq, ← hOwnLevels ρ L hL ht top]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    exact congrArg Prod.snd (hf ls (fun j hj => (List.mem_sublists.mp hls).subset hj) (p,0))
  have hOwnRight (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) (top p : ℕ) :
      (erase ρ L).rightExt (ρ.sideAt L) top p = (trunc ρ L).rightExt (ρ.sideAt L) top p := by
    have hf : ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase ρ L).levelsOn (ρ.sideAt L) top) →
        ∀ z, ls.foldl (rightStep (erase ρ L)) z = ls.foldl (rightStep (trunc ρ L)) z := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hj z
        simp only [List.foldl_cons, rightStep, hOwnExt ρ L hL ht top j (hj j (by simp))]
        exact ih (fun i hi => hj i (by simp [hi])) _
    rw [rightExt_eq, rightExt_eq, ← hOwnLevels ρ L hL ht top]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    exact congrArg Prod.snd (hf ls (fun j hj => (List.mem_sublists.mp hls).subset hj) (p,0))
  have hOwnChain (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) (p q : ℕ) :
      (erase ρ L).chainExt (ρ.sideAt L) p q = (trunc ρ L).chainExt (ρ.sideAt L) p q := by
    simp only [chainExt, hOwnLeft ρ L hL ht, hOwnRight ρ L hL ht]
  have hOwnJoin (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) (p q : ℕ) :
      (erase ρ L).joinExt (ρ.sideAt L) p q = (trunc ρ L).joinExt (ρ.sideAt L) p q := by
    simp only [joinExt, hOwnChain ρ L hL ht, ← hOwnLevels ρ L hL ht 0]
    congr 1
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro j hj
    rw [hOwnLeft ρ L hL ht, hOwnRight ρ L hL ht, hOwnMaximum ρ L hL ht 0 j hj]
  have hMaxAppend (A B : List ℕ) :
      ((A ++ B).max?).getD 0 = max (A.max?.getD 0) (B.max?.getD 0) := by
    apply le_antisymm
    · apply getD_max?_le
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (le_getD_max?_of_mem hz).trans (le_max_left _ _)
      · exact (le_getD_max?_of_mem hz).trans (le_max_right _ _)
    · apply max_le
      · apply getD_max?_le_of_forall
        intro z hz
        exact ⟨z, List.mem_append_left _ hz, le_rfl⟩
      · apply getD_max?_le_of_forall
        intro z hz
        exact ⟨z, List.mem_append_right _ hz, le_rfl⟩
  have hMaxShift (A : List ℕ) (n : ℕ) (hne : A ≠ []) :
      ((A.map (· + n)).max?).getD 0 = A.max?.getD 0 + n := by
    apply le_antisymm
    · apply getD_max?_le
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact Nat.add_le_add_right (le_getD_max?_of_mem hy) n
    · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil A hne
      have h0 : n ≤ ((A.map (· + n)).max?).getD 0 :=
        (Nat.le_add_left n y).trans
          (le_getD_max?_of_mem (List.mem_map.mpr ⟨y,hy,rfl⟩))
      have hm : A.max?.getD 0 ≤ ((A.map (· + n)).max?).getD 0 - n := by
        apply getD_max?_le
        intro z hz
        have h := le_getD_max?_of_mem (List.mem_map.mpr ⟨z,hz,rfl⟩ :
          z+n ∈ A.map (· + n))
        omega
      omega
  have hTruncLevels (ρ : Context) (L : ℕ) :
      (trunc ρ L).levels = ρ.levels.filter (· < L) := by
    apply (hSorted (trunc ρ L)).eq_of_mem_iff ((hSorted ρ).filter _)
    intro j
    simp only [List.mem_filter, hLevelMem, hTruncMax, List.length_take,
      decide_eq_true_eq]
    omega
  have hTruncLevelsOn (ρ : Context) (L : ℕ) (v : Side) (top : ℕ) :
      (trunc ρ L).levelsOn v top = (ρ.levelsOn v top).filter (· < L) := by
    simp only [levelsOn, hTruncLevels, hTruncSide, List.filter_filter]
    apply List.filter_congr
    intro j _
    simp only [Bool.and_comm]
  have hTruncPure (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) :
      (trunc ρ L).levelsOn v 0 = ρ.levelsOn v L := by
    rw [hTruncLevelsOn]
    simp only [levelsOn, List.filter_filter]
    apply List.filter_congr
    intro j _
    simp [show L ≠ 0 by omega, Bool.and_comm]
  have hTruncYoung (ρ : Context) (L top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L)
      (v : Side) : (trunc ρ L).levelsOn v top = ρ.levelsOn v top := by
    rw [hTruncLevelsOn]
    apply List.filter_eq_self.mpr
    intro j hj
    have hc : ρ.sideAt j = v ∧ (top = 0 ∨ j < top) :=
      of_decide_eq_true (List.mem_filter.mp hj).2
    simp only [decide_eq_true_eq]
    omega
  have hTruncLeftStep (ρ : Context) (L : ℕ) : leftStep (trunc ρ L) = leftStep ρ := by
    funext z j
    simp only [leftStep, hTruncExt]
  have hTruncRightStep (ρ : Context) (L : ℕ) :
      rightStep (trunc ρ L) = rightStep ρ := by
    funext z j
    simp only [rightStep, hTruncExt]
  have hTruncLeftPure (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) (p : ℕ) :
      (trunc ρ L).leftExt v 0 p = ρ.leftExt v L p := by
    simp only [leftExt_eq, hTruncPure ρ L hL, hTruncLeftStep]
  have hTruncRightPure (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (v : Side) (p : ℕ) :
      (trunc ρ L).rightExt v 0 p = ρ.rightExt v L p := by
    simp only [rightExt_eq, hTruncPure ρ L hL, hTruncRightStep]
  have hTruncLeftYoung (ρ : Context) (L top : ℕ) (htop : 1 ≤ top)
      (htL : top ≤ L) (v : Side) (p : ℕ) :
      (trunc ρ L).leftExt v top p = ρ.leftExt v top p := by
    simp only [leftExt_eq, hTruncYoung ρ L top htop htL, hTruncLeftStep]
  have hTruncRightYoung (ρ : Context) (L top : ℕ) (htop : 1 ≤ top)
      (htL : top ≤ L) (v : Side) (p : ℕ) :
      (trunc ρ L).rightExt v top p = ρ.rightExt v top p := by
    simp only [rightExt_eq, hTruncYoung ρ L top htop htL, hTruncRightStep]
  have hSourceOwnLevels (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) :
      ρ.levelsOn (ρ.sideAt L) 0 = ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
    have hLs : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by simp [levelsOn, hL]
    have hs : (ρ.levelsOn (ρ.sideAt L) L ++ [L]).Pairwise (· < ·) := by
      apply List.pairwise_append.mpr
      refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
      intro i hi j hj
      have he : j = L := by simpa using hj
      subst j
      have hc : ρ.sideAt i = ρ.sideAt L ∧ (L = 0 ∨ i < L) :=
        of_decide_eq_true (List.mem_filter.mp hi).2
      have hL1 := one_le_of_mem_levels hL
      omega
    apply ((hSorted ρ).filter _).eq_of_mem_iff hs
    intro j
    constructor
    · intro hj
      have hjL := ht j hj
      by_cases he : j = L
      · simp [he]
      · apply List.mem_append.mpr
        left
        apply List.mem_filter.mpr
        refine ⟨(List.mem_filter.mp hj).1, ?_⟩
        apply decide_eq_true
        have hc : ρ.sideAt j = ρ.sideAt L ∧ (0 = 0 ∨ j < 0) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        exact ⟨hc.1, Or.inr (by omega)⟩
    · intro hj
      rcases List.mem_append.mp hj with hj | hj
      · apply List.mem_filter.mpr
        refine ⟨(List.mem_filter.mp hj).1, ?_⟩
        apply decide_eq_true
        have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        exact ⟨hc.1, Or.inl rfl⟩
      · have he : j = L := by simpa using hj
        simpa [levelsOn, he] using hLs
  have hFoldBoundary (ρ : Context) (x : ℕ) (dir : Bool) :
      ∀ (ls : List ℕ),
      (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, if dir then y < x else x < y) →
      ∀ z : ℕ × ℕ, (if dir then z.1 < x else x < z.1) →
      (if dir then (ls.foldl (leftStep ρ) z).1 < x
        else x < (ls.foldl (leftStep ρ) z).1) ∧
      (if dir then (ls.foldl (rightStep ρ) z).1 < x
        else x < (ls.foldl (rightStep ρ) z).1) := by
    intro ls
    induction ls with
    | nil => intro _ z hz; exact ⟨hz,hz⟩
    | cons j ls ih =>
      intro hy z hz
      have ht := fun i hi y hiy => hy i (List.mem_cons_of_mem j hi) y hiy
      constructor
      · cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? with
        | none => simpa only [List.foldl_cons, leftStep, hh] using (ih ht z hz).1
        | some y =>
          have hm := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
          have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
          simpa only [List.foldl_cons, leftStep, hh] using (ih ht (y,z.2+1) hyx).1
      · cases hh : ((ρ.extPositions j).filter (z.1 < ·)).head? with
        | none => simpa only [List.foldl_cons, rightStep, hh] using (ih ht z hz).2
        | some y =>
          have hm := List.mem_of_mem_head? (Option.mem_def.mpr hh)
          have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
          simpa only [List.foldl_cons, rightStep, hh] using (ih ht (y,z.2+1) hyx).2
  have hSourceLeft (ρ : Context) (L x : ℕ) (hL : L ∈ ρ.levels)
      (hsingle : ρ.extPositions L = [x]) (dir : Bool)
      (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L)
      (p : ℕ) (hp : p ∈ ρ.childPositions) :
      ρ.leftExt (ρ.sideAt L) 0 p =
        ρ.leftExt (ρ.sideAt L) L p + (if dir then 0 else 1) := by
    let A := (ρ.levelsOn (ρ.sideAt L) L).sublists
    let f := fun ls : List ℕ => (ls.foldl (leftStep ρ) (p,0)).2
    have heach (ls : List ℕ) (hls : ls ∈ A) :
        f (ls ++ [L]) = f ls + (if dir then 0 else 1) := by
      let z := ls.foldl (leftStep ρ) (p,0)
      have hz := (hFoldBoundary ρ x dir ls
        (fun j hj y hiy => hy j (List.mem_sublists.mp hls |>.subset hj) y hiy)
        (p,0) (hc p hp)).1
      change (if dir then z.1 < x else x < z.1) at hz
      dsimp only [f]
      rw [List.foldl_append]
      change (leftStep ρ z L).2 = z.2 + (if dir then 0 else 1)
      cases dir with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hz ⊢
        simp [leftStep, hsingle, hz]
      | true =>
        simp only [if_true] at hz ⊢
        simp [leftStep, hsingle, show ¬x < z.1 by omega]
    have hm : (A.map (fun ls => ls ++ [L])).map f =
        (A.map f).map (· + (if dir then 0 else 1)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro ls hls
      exact heach ls hls
    have hne : A.map f ≠ [] := by
      intro hn
      have h0 : 0 ∈ A.map f :=
        List.mem_map.mpr ⟨[], List.mem_sublists.mpr (List.nil_sublist _), rfl⟩
      rw [hn] at h0
      simp at h0
    rw [leftExt_eq, hSourceOwnLevels ρ L hL ht, List.sublists_concat,
      List.map_append, hMaxAppend]
    change max ((A.map f).max?.getD 0)
      (((A.map (fun ls => ls ++ [L])).map f).max?.getD 0) =
      ρ.leftExt (ρ.sideAt L) L p + (if dir then 0 else 1)
    rw [hm, hMaxShift _ _ hne]
    change max (ρ.leftExt (ρ.sideAt L) L p)
      (ρ.leftExt (ρ.sideAt L) L p + (if dir then 0 else 1)) =
      ρ.leftExt (ρ.sideAt L) L p + (if dir then 0 else 1)
    exact max_eq_right (Nat.le_add_right _ _)
  have hSourceRight (ρ : Context) (L x : ℕ) (hL : L ∈ ρ.levels)
      (hsingle : ρ.extPositions L = [x]) (dir : Bool)
      (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L)
      (p : ℕ) (hp : p ∈ ρ.childPositions) :
      ρ.rightExt (ρ.sideAt L) 0 p =
        ρ.rightExt (ρ.sideAt L) L p + (if dir then 1 else 0) := by
    let A := (ρ.levelsOn (ρ.sideAt L) L).sublists
    let f := fun ls : List ℕ => (ls.foldl (rightStep ρ) (p,0)).2
    have heach (ls : List ℕ) (hls : ls ∈ A) :
        f (ls ++ [L]) = f ls + (if dir then 1 else 0) := by
      let z := ls.foldl (rightStep ρ) (p,0)
      have hz := (hFoldBoundary ρ x dir ls
        (fun j hj y hiy => hy j (List.mem_sublists.mp hls |>.subset hj) y hiy)
        (p,0) (hc p hp)).2
      change (if dir then z.1 < x else x < z.1) at hz
      dsimp only [f]
      rw [List.foldl_append]
      change (rightStep ρ z L).2 = z.2 + (if dir then 1 else 0)
      cases dir with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hz ⊢
        simp [rightStep, hsingle, show ¬z.1 < x by omega]
      | true =>
        simp only [if_true] at hz ⊢
        simp [rightStep, hsingle, hz]
    have hm : (A.map (fun ls => ls ++ [L])).map f =
        (A.map f).map (· + (if dir then 1 else 0)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro ls hls
      exact heach ls hls
    have hne : A.map f ≠ [] := by
      intro hn
      have h0 : 0 ∈ A.map f :=
        List.mem_map.mpr ⟨[], List.mem_sublists.mpr (List.nil_sublist _), rfl⟩
      rw [hn] at h0
      simp at h0
    rw [rightExt_eq, hSourceOwnLevels ρ L hL ht, List.sublists_concat,
      List.map_append, hMaxAppend]
    change max ((A.map f).max?.getD 0)
      (((A.map (fun ls => ls ++ [L])).map f).max?.getD 0) =
      ρ.rightExt (ρ.sideAt L) L p + (if dir then 1 else 0)
    rw [hm, hMaxShift _ _ hne]
    change max (ρ.rightExt (ρ.sideAt L) L p)
      (ρ.rightExt (ρ.sideAt L) L p + (if dir then 1 else 0)) =
      ρ.rightExt (ρ.sideAt L) L p + (if dir then 1 else 0)
    exact max_eq_right (Nat.le_add_right _ _)
  have hSourceChain (ρ : Context) (L x : ℕ) (hL : L ∈ ρ.levels)
      (hsingle : ρ.extPositions L = [x]) (dir : Bool)
      (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      ρ.chainExt (ρ.sideAt L) p q = (trunc ρ L).chainExt (ρ.sideAt L) p q + 1 := by
    have hL1 := one_le_of_mem_levels hL
    simp only [chainExt, hSourceLeft ρ L x hL hsingle dir hc hy ht p hp,
      hSourceRight ρ L x hL hsingle dir hc hy ht q hq,
      hTruncLeftPure ρ L hL1, hTruncRightPure ρ L hL1]
    cases dir <;> simp <;> omega
  have hTruncMaximumYoung (ρ : Context) (L j : ℕ) (hj : 1 ≤ j) (hjL : j < L) :
      (trunc ρ L).maximumAt j = ρ.maximumAt j := by
    simp only [maximumAt, hTruncMax, List.getElem?_take_of_lt (by omega : j-1 < L-1)]
  have hSourceJoin (ρ : Context) (L x : ℕ) (hL : L ∈ ρ.levels)
      (hsingle : ρ.extPositions L = [x]) (hmax : 1 ≤ ρ.maximumAt L) (dir : Bool)
      (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      ρ.joinExt (ρ.sideAt L) p q = max ((trunc ρ L).joinExt (ρ.sideAt L) p q)
        ((trunc ρ L).chainExt (ρ.sideAt L) p q + ρ.maximumAt L) := by
    have hL1 := one_le_of_mem_levels hL
    have hm : (ρ.levelsOn (ρ.sideAt L) L).map
        (fun j => ρ.leftExt (ρ.sideAt L) j p + ρ.rightExt (ρ.sideAt L) j q +
          ρ.maximumAt j) =
        ((trunc ρ L).levelsOn (ρ.sideAt L) 0).map
        (fun j => (trunc ρ L).leftExt (ρ.sideAt L) j p +
          (trunc ρ L).rightExt (ρ.sideAt L) j q + (trunc ρ L).maximumAt j) := by
      rw [hTruncPure ρ L hL1]
      apply List.map_congr_left
      intro j hj
      have hj1 := (one_le_of_mem_levelsOn hj).1
      have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      have hjL : j < L := by omega
      rw [hTruncLeftYoung ρ L j hj1 (by omega),
        hTruncRightYoung ρ L j hj1 (by omega), hTruncMaximumYoung ρ L j hj1 hjL]
    have hc' := hSourceChain ρ L x hL hsingle dir hc hy ht p q hp hq
    have hcy : ρ.leftExt (ρ.sideAt L) L p + ρ.rightExt (ρ.sideAt L) L q =
        (trunc ρ L).chainExt (ρ.sideAt L) p q := by
      simp only [chainExt, hTruncLeftPure ρ L hL1, hTruncRightPure ρ L hL1]
    rw [joinExt, hSourceOwnLevels ρ L hL ht, List.map_append, hMaxAppend, hm]
    simp only [List.map_cons, List.map_nil, List.max?_singleton, Option.getD_some]
    rw [hc', hcy]
    simp only [joinExt]
    omega
  have hUpMono (L i j : ℕ) (h : i < j) : up L i < up L j := by
    dsimp [up]
    split_ifs <;> omega
  have hUpZero (L : ℕ) (hL : 1 ≤ L) : up L 0 = 0 := by
    simp [up, show 0 < L by omega]
  have hOppLevels (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side)
      (hv : v ≠ ρ.sideAt L) (top : ℕ) :
      (((erase ρ L).levelsOn v top).map (up L)) = ρ.levelsOn v (up L top) := by
    have hs : (((erase ρ L).levelsOn v top).map (up L)).Pairwise (· < ·) :=
      ((hSorted (erase ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
    apply hs.eq_of_mem_iff ((hSorted ρ).filter _)
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hjl := (List.mem_filter.mp hj).1
      have hjc : (erase ρ L).sideAt j = v ∧ (top = 0 ∨ j < top) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      apply List.mem_filter.mpr
      refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
      apply decide_eq_true
      refine ⟨?_, ?_⟩
      · rw [← hSide ρ L j hL hjl]
        exact hjc.1
      · rcases hjc.2 with rfl | hlt
        · exact Or.inl (hUpZero L (one_le_of_mem_levels hL))
        · exact Or.inr (hUpMono L j top hlt)
    · intro hi
      have hil := (List.mem_filter.mp hi).1
      have hic : ρ.sideAt i = v ∧ (up L top = 0 ∨ i < up L top) :=
        of_decide_eq_true (List.mem_filter.mp hi).2
      have hiL : i ≠ L := by
        intro he
        subst i
        exact hv hic.1.symm
      let j := if i < L then i else i-1
      have hLr := (hLevelMem ρ L).mp hL
      have hir := (hLevelMem ρ i).mp hil
      have hjr : 1 ≤ j ∧ j < ρ.maxima.length ∧ up L j = i := by
        dsimp [j, up]
        split_ifs <;> omega
      have hjl : j ∈ (erase ρ L).levels := by
        apply (hLevelMem (erase ρ L) j).mpr
        rw [hDepth ρ L hL]
        omega
      apply List.mem_map.mpr
      refine ⟨j, ?_, hjr.2.2⟩
      apply List.mem_filter.mpr
      refine ⟨hjl, ?_⟩
      apply decide_eq_true
      refine ⟨?_, ?_⟩
      · rw [hSide ρ L j hL hjl, hjr.2.2]
        exact hic.1
      · rcases hic.2 with hzero | hlt
        · left
          by_contra hne
          have h := hUpMono L 0 top (by omega)
          rw [hUpZero L hLr.1, hzero] at h
          omega
        · right
          by_contra hn
          have hm : up L top ≤ up L j := by
            rcases lt_or_eq_of_le (show top ≤ j by omega) with hm | he
            · exact (hUpMono L top j hm).le
            · rw [he]
          rw [hjr.2.2] at hm
          omega
  have hFoldEraseLeft (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase ρ L).levels) → ∀ z,
      ls.foldl (leftStep (erase ρ L)) z = (ls.map (up L)).foldl (leftStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, leftStep,
        hExt ρ L j hL (hj j (by simp))]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hFoldEraseRight (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase ρ L).levels) → ∀ z,
      ls.foldl (rightStep (erase ρ L)) z = (ls.map (up L)).foldl (rightStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, rightStep,
        hExt ρ L j hL (hj j (by simp))]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hOppLeft (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side)
      (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
      (erase ρ L).leftExt v top p = ρ.leftExt v (up L top) p := by
    rw [leftExt_eq, leftExt_eq, ← hOppLevels ρ L hL v hv top,
      List.sublists_map, List.map_map]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    exact congrArg Prod.snd (hFoldEraseLeft ρ L hL ls
      (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) (p,0))
  have hOppRight (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side)
      (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
      (erase ρ L).rightExt v top p = ρ.rightExt v (up L top) p := by
    rw [rightExt_eq, rightExt_eq, ← hOppLevels ρ L hL v hv top,
      List.sublists_map, List.map_map]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    exact congrArg Prod.snd (hFoldEraseRight ρ L hL ls
      (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) (p,0))
  have hOppChain (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side)
      (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
      (erase ρ L).chainExt v p q = ρ.chainExt v p q := by
    simp only [chainExt, hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
      hUpZero L (one_le_of_mem_levels hL)]
  have hOppJoin (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side)
      (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
      (erase ρ L).joinExt v p q = ρ.joinExt v p q := by
    have hl : (((erase ρ L).levelsOn v 0).map (up L)) = ρ.levelsOn v 0 := by
      simpa only [hUpZero L (one_le_of_mem_levels hL)] using hOppLevels ρ L hL v hv 0
    rw [joinExt, joinExt, hOppChain ρ L hL v hv, ← hl, List.map_map]
    congr 1
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro j hj
    rw [hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
      hMaximum ρ L j hL (List.mem_filter.mp hj).1]
    rfl
  have hCaps (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (L x : ℕ) (hL : L ∈ ρ.levels) (hsingle : ρ.extPositions L = [x])
      (hmax : 1 ≤ ρ.maximumAt L)
      (dir : Bool) (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      ρ.cupLimit p q = (norm ρ L).cupLimit p q ∧
      ρ.capLimit p q = (norm ρ L).capLimit p q := by
    have hc' := hSourceChain ρ L x hL hsingle dir hc hy ht p q hp hq
    have hj' := hSourceJoin ρ L x hL hsingle hmax dir hc hy ht p q hp hq
    rw [← hOwnChain ρ L hL ht] at hc' hj'
    rw [← hOwnJoin ρ L hL ht] at hj'
    cases hs : ρ.sideAt L with
    | lower =>
      rw [hs] at hc' hj'
      have hOC := hOppChain ρ L hL Side.upper (by simp [hs]) p q
      have hOJ := hOppJoin ρ L hL Side.upper (by simp [hs]) p q
      simp only [norm, hs]
      change
        min (ρ.u - 1 - ρ.chainExt Side.lower p q) (ρ.k - 1 - ρ.joinExt Side.lower p q) =
          min (min (ρ.u-1) (ρ.k-ρ.maximumAt L) - 1 - (erase ρ L).chainExt Side.lower p q)
            (ρ.k - 1 - (erase ρ L).joinExt Side.lower p q) ∧
        min (ρ.a - 1 - ρ.chainExt Side.upper p q) (ρ.k - 1 - ρ.joinExt Side.upper p q) =
          min (ρ.a - 1 - (erase ρ L).chainExt Side.upper p q)
            (ρ.k - 1 - (erase ρ L).joinExt Side.upper p q)
      rw [hc', hj', hOC, hOJ]
      constructor
      · omega
      · rfl
    | upper =>
      rw [hs] at hc' hj'
      have hOC := hOppChain ρ L hL Side.lower (by simp [hs]) p q
      have hOJ := hOppJoin ρ L hL Side.lower (by simp [hs]) p q
      simp only [norm, hs]
      change
        min (ρ.u - 1 - ρ.chainExt Side.lower p q) (ρ.k - 1 - ρ.joinExt Side.lower p q) =
          min (ρ.u - 1 - (erase ρ L).chainExt Side.lower p q)
            (ρ.k - 1 - (erase ρ L).joinExt Side.lower p q) ∧
        min (ρ.a - 1 - ρ.chainExt Side.upper p q) (ρ.k - 1 - ρ.joinExt Side.upper p q) =
          min (min (ρ.a-1) (ρ.k-ρ.maximumAt L) - 1 - (erase ρ L).chainExt Side.upper p q)
            (ρ.k - 1 - (erase ρ L).joinExt Side.upper p q)
      rw [hc', hj', hOC, hOJ]
      constructor
      · rfl
      · omega
  have hErasePart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL : 1 ≤ L) :
      erase (ρ.part keep v m) (L+1) = (erase ρ L).part keep v m := by
    have hi (j : ℕ) : idx (ρ.maxima.length+1) (L+1) (j+1) = idx ρ.maxima.length L j + 1 := by
      dsimp [idx]; split_ifs <;> omega
    have hnew : idx (ρ.maxima.length+1) (L+1) 1 = 1 := by simp [idx]; omega
    have hm : (m :: ρ.maxima).eraseIdx (L+1-1) = m :: ρ.maxima.eraseIdx (L-1) := by
      rw [show L+1-1 = (L-1)+1 by omega, List.eraseIdx_cons_succ]
    have hw : (erase (ρ.part keep v m) (L+1)).word = ((erase ρ L).part keep v m).word := by
      change ((ρ.part keep v m).word.map (letter (m :: ρ.maxima).length (L+1))) =
        (List.range (erase ρ L).word.length).map (fun p => match (erase ρ L).letterAt p with
          | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
          | Letter.ext j w => Letter.ext (j+1) w)
      rw [hLen]
      simp only [part, List.map_map, List.length_cons, Function.comp_def]
      apply List.map_congr_left
      intro p _
      rw [hLetter]
      cases ρ.letterAt p with
      | child => by_cases hp : p ∈ keep <;> simp [hp, letter, hnew]
      | ext j w => simp only [letter, hi]
    change Context.mk ρ.a ρ.u ρ.k _ ((m :: ρ.maxima).eraseIdx (L+1-1)) =
      Context.mk ρ.a ρ.u ρ.k _ (m :: ρ.maxima.eraseIdx (L-1))
    rw [hm]
    exact congrArg (fun w => Context.mk ρ.a ρ.u ρ.k w (m :: ρ.maxima.eraseIdx (L-1))) hw
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
  have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL : 1 ≤ L) :
      norm (ρ.part keep v m) (L+1) = (norm ρ L).part keep v m := by
    have hs := part_sideAt_succ ρ keep v m hL
    have hM := part_maximumAt_succ ρ keep v m hL
    have he := hErasePart ρ keep v m L hL
    simp only [norm, hs, hM, he]
    cases hh : ρ.sideAt L <;> rfl
  have hNextTerminal (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L)
      (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) 0, j ≤ L+1 := by
    intro j hj
    have hj1 := (one_le_of_mem_levelsOn hj).1
    have hL1 := one_le_of_mem_levels hL
    by_cases he : j = 1
    · omega
    · let i := j-1
      have hi : 1 ≤ i := by dsimp [i]; omega
      have he : j = i+1 := by dsimp [i]; omega
      rw [he] at hj ⊢
      have hjLevel : i+1 ∈ (ρ.part keep v m).levels := (List.mem_filter.mp hj).1
      rw [part_levels] at hjLevel
      have hiLevel : i ∈ ρ.levels := by
        rcases List.mem_cons.mp hjLevel with h | h
        · omega
        · obtain ⟨z, hz, hzi⟩ := List.mem_map.mp h
          have hz' : z = i := by omega
          simpa only [hz'] using hz
      have hjc : (ρ.part keep v m).sideAt (i+1) = (ρ.part keep v m).sideAt (L+1) ∧
          (0 = 0 ∨ i+1 < 0) := of_decide_eq_true (List.mem_filter.mp hj).2
      rw [part_sideAt_succ ρ keep v m hi, part_sideAt_succ ρ keep v m hL1] at hjc
      have hiOn : i ∈ ρ.levelsOn (ρ.sideAt L) 0 :=
        List.mem_filter.mpr ⟨hiLevel, by simp [hjc.1]⟩
      have := ht i hiOn
      omega
  have hBase (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (L x : ℕ) (hL : L ∈ ρ.levels) (hsingle : ρ.extPositions L = [x])
      (hmax : 1 ≤ ρ.maximumAt L)
      (dir : Bool) (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) :
      ρ.base = (norm ρ L).base := by
    rw [base_eq_baseOf, base_eq_baseOf, hNormChild]
    cases hh : ρ.childPositions.head? with
    | none => rfl
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      have h := hCaps ρ hPos L x hL hsingle hmax dir hc hy ht p p hp hp
      simp only [baseOf, h.1, h.2, hNormK]
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      ∀ (L x : ℕ), L ∈ ρ.levels → ρ.extPositions L = [x] →
      1 ≤ ρ.maximumAt L → ∀ dir : Bool,
      (∀ p ∈ ρ.childPositions, if dir then p < x else x < p) →
      (∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p) →
      (∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) →
      boundFuel fuel ρ = boundFuel fuel (norm ρ L) := by
    intro fuel
    induction fuel with
    | zero => intro ρ hPos L x hL hsingle hmax dir hc hy ht; rfl
    | succ fuel ih =>
      intro ρ hPos L x hL hsingle hmax dir hc hy ht
      have hL1 := one_le_of_mem_levels hL
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) = boundFuel fuel ((norm ρ L).part keep v m) := by
        have hn : L+1 ∈ (ρ.part keep v m).levels := by
          rw [part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L,hL,rfl⟩)
        have hs' : (ρ.part keep v m).extPositions (L+1) = [x] := by
          rw [part_extPositions_succ ρ keep v m hL1, hsingle]
        have hm' : 1 ≤ (ρ.part keep v m).maximumAt (L+1) := by
          rw [part_maximumAt_succ ρ keep v m hL1]
          exact hmax
        have hd := hNextBoundary ρ hPos L x hL dir hc hy keep v m
        have h := ih (ρ.part keep v m) (hPartPositive ρ keep v m)
          (L+1) x hn hs' hm' dir hd.1 hd.2 (hNextTerminal ρ L hL ht keep v m)
        rw [hNormPart ρ keep v m L hL1] at h
        exact h
      simp only [boundFuel, hNormRuns, hNormChild, hNormBlocks, hNormK]
      split_ifs
      · exact hBase ρ hPos L x hL hsingle hmax dir hc hy ht
      · congr 1
        apply congrArg List.max?
        apply List.flatMap_congr
        intro keep _
        apply List.flatMap_congr
        intro m _
        simp only [hParts]
  refine ⟨fun p hp q hq => hCaps σ hpositive N x hN hsole hmaximum
    rightward hchildren hyounger hterminal p q hp hq,
    fun fuel => hFuel fuel σ hpositive N x hN hsole hmaximum
      rightward hchildren hyounger hterminal, ?_⟩
  simpa only [bound, hNormChild] using
    hFuel (σ.childPositions.length+1) σ hpositive N x hN hsole hmaximum
      rightward hchildren hyounger hterminal

end ErdosSzekeres
