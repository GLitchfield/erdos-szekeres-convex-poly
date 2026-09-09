import ESBlueprint.B.CtxBoundaryMarkerEraseNormalize

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Absorb an indexed sibling maximum into its global capacity while erasing only its own level and retaining every older opposite-axis history level. The selected level is oldest on its axis; cap that global at min(global,k-maximum), preserve the child/external pattern, and increase every endpoint cup/cap limit, every same-fuel bound and the full recursive bound. Indexed membership and the oldest-on-axis condition suffice, with no boundary geometry, positive-label or actual-marker-position premise. Extends sibling-maximum normalization without discarding older opposite markers, supplying a needed comparison toward the critical saturated capacity-three sandwich case. Also gives exact child positions, depth reduction and every surviving indexed level's source index, external positions, side and sibling maximum, so downstream marker comparisons can reuse the transport directly.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_oldest_axis_maximum_erase_normalize (σ : Ctx.Context) (N : ℕ) (hN : N ∈ σ.levels)
  (hterminal : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, j ≤ N) :
  let ρ : Ctx.Context := { σ with
    word := σ.word.map (fun z => match z with
      | Ctx.Letter.child => Ctx.Letter.child
      | Ctx.Letter.ext j v => Ctx.Letter.ext
          (if j = N then σ.maxima.length else if N < j then j - 1 else j) v)
    maxima := σ.maxima.eraseIdx (N - 1) }
  let τ : Ctx.Context := match σ.sideAt N with
    | Ctx.Side.lower => { ρ with u := min σ.u (σ.k - σ.maximumAt N) }
    | Ctx.Side.upper => { ρ with a := min σ.a (σ.k - σ.maximumAt N) }
  τ.childPositions = σ.childPositions ∧ τ.maxima.length = σ.maxima.length - 1 ∧
    (∀ j ∈ τ.levels,
      let i := if j < N then j else j + 1
      i ∈ σ.levels ∧ i ≠ N ∧ τ.extPositions j = σ.extPositions i ∧
        τ.sideAt j = σ.sideAt i ∧ τ.maximumAt j = σ.maximumAt i) ∧
  (∀ p q,
    σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧
    σ.bound ≤ τ.bound := by
  classical
  let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
  let letter (D L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext (idx D L j) v
  let erase (ρ : Context) (L : ℕ) : Context :=
    { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L-1) }
  let up (L j : ℕ) := if j < L then j else j+1
  let norm (ρ : Context) (L : ℕ) : Context := match ρ.sideAt L with
    | Side.lower => { erase ρ L with u := min ρ.u (ρ.k-ρ.maximumAt L) }
    | Side.upper => { erase ρ L with a := min ρ.a (ρ.k-ρ.maximumAt L) }
  let trunc (ρ : Context) (L : ℕ) : Context := match ρ.sideAt L with
    | Side.lower => { ρ with u := min ρ.u (ρ.k-ρ.maximumAt L), maxima := ρ.maxima.take (L-1) }
    | Side.upper => { ρ with a := min ρ.a (ρ.k-ρ.maximumAt L), maxima := ρ.maxima.take (L-1) }
  change (norm σ N).childPositions = σ.childPositions ∧
    (norm σ N).maxima.length = σ.maxima.length - 1 ∧
    (∀ j ∈ (norm σ N).levels,
      up N j ∈ σ.levels ∧ up N j ≠ N ∧
        (norm σ N).extPositions j = σ.extPositions (up N j) ∧
        (norm σ N).sideAt j = σ.sideAt (up N j) ∧
        (norm σ N).maximumAt j = σ.maximumAt (up N j)) ∧
    (∀ p q, σ.cupLimit p q ≤ (norm σ N).cupLimit p q ∧
      σ.capLimit p q ≤ (norm σ N).capLimit p q) ∧
    (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel (norm σ N)) ∧ σ.bound ≤ (norm σ N).bound
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
  have hCaps (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) (p q : ℕ) :
      ρ.cupLimit p q ≤ (norm ρ L).cupLimit p q ∧
      ρ.capLimit p q ≤ (norm ρ L).capLimit p q := by
    have hE := (ctx_erase_level_bound_mono ρ L hL).1 p q
    change ρ.cupLimit p q ≤ (erase ρ L).cupLimit p q ∧
      ρ.capLimit p q ≤ (erase ρ L).capLimit p q at hE
    have hB := (ctx_sibling_maximum_upper_normalize ρ L hL).1 p q
    change ρ.cupLimit p q ≤ (trunc ρ L).cupLimit p q ∧
      ρ.capLimit p q ≤ (trunc ρ L).capLimit p q at hB
    have hC := hOwnChain ρ L hL ht p q
    have hJ := hOwnJoin ρ L hL ht p q
    cases hs : ρ.sideAt L with
    | lower =>
      rw [hs] at hC hJ
      have he : (norm ρ L).cupLimit p q = (trunc ρ L).cupLimit p q := by
        have hc' : (norm ρ L).chainExt Side.lower p q = (trunc ρ L).chainExt Side.lower p q := by
          simpa only [norm, hs] using hC
        have hj' : (norm ρ L).joinExt Side.lower p q = (trunc ρ L).joinExt Side.lower p q := by
          simpa only [norm, hs] using hJ
        have hg : (norm ρ L).u = (trunc ρ L).u := by simp only [norm, trunc, hs]
        have hk : (norm ρ L).k = (trunc ρ L).k := by simp only [norm, trunc, hs]; rfl
        simp only [cupLimit, hc', hj', hg, hk]
      have ho : (erase ρ L).capLimit p q = (norm ρ L).capLimit p q := by
        simp only [norm, hs]
        rfl
      exact ⟨hB.1.trans (le_of_eq he.symm), hE.2.trans (le_of_eq ho)⟩
    | upper =>
      rw [hs] at hC hJ
      have he : (norm ρ L).capLimit p q = (trunc ρ L).capLimit p q := by
        have hc' : (norm ρ L).chainExt Side.upper p q = (trunc ρ L).chainExt Side.upper p q := by
          simpa only [norm, hs] using hC
        have hj' : (norm ρ L).joinExt Side.upper p q = (trunc ρ L).joinExt Side.upper p q := by
          simpa only [norm, hs] using hJ
        have hg : (norm ρ L).a = (trunc ρ L).a := by simp only [norm, trunc, hs]
        have hk : (norm ρ L).k = (trunc ρ L).k := by simp only [norm, trunc, hs]; rfl
        simp only [capLimit, hc', hj', hg, hk]
      have ho : (erase ρ L).cupLimit p q = (norm ρ L).cupLimit p q := by
        simp only [norm, hs]
        rfl
      exact ⟨hE.1.trans (le_of_eq ho), hB.2.trans (le_of_eq he.symm)⟩
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
  have hBase (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) : ρ.base ≤ (norm ρ L).base := by
    rw [base_eq_baseOf, base_eq_baseOf, hNormChild]
    cases hh : ρ.childPositions.head? with
    | none => exact le_rfl
    | some p =>
      have h := hCaps ρ L hL ht p p
      simpa only [hNormK] using baseOf_mono (k := ρ.k) h.1 h.2
  have hFuel : ∀ fuel (ρ : Context) (L : ℕ), L ∈ ρ.levels →
      (∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) →
      boundFuel fuel ρ ≤ boundFuel fuel (norm ρ L) := by
    intro fuel
    induction fuel with
    | zero => intro ρ L hL ht; exact le_rfl
    | succ fuel ih =>
      intro ρ L hL ht
      have hL1 := one_le_of_mem_levels hL
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel ((norm ρ L).part keep v m) := by
        have hn : L+1 ∈ (ρ.part keep v m).levels := by
          rw [part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L,hL,rfl⟩)
        have h := ih (ρ.part keep v m) (L+1) hn (hNextTerminal ρ L hL ht keep v m)
        rw [hNormPart ρ keep v m L hL1] at h
        exact h
      simp only [boundFuel, hNormRuns, hNormChild, hNormBlocks, hNormK]
      split_ifs
      · exact hBase ρ L hL ht
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
  have hNormDepth : (norm σ N).maxima.length = σ.maxima.length - 1 := by
    cases hs : σ.sideAt N <;> simpa only [norm, hs] using hDepth σ N hN
  have hHistory (j : ℕ) (hj : j ∈ (norm σ N).levels) :
      up N j ∈ σ.levels ∧ up N j ≠ N ∧
        (norm σ N).extPositions j = σ.extPositions (up N j) ∧
        (norm σ N).sideAt j = σ.sideAt (up N j) ∧
        (norm σ N).maximumAt j = σ.maximumAt (up N j) := by
    have hje : j ∈ (erase σ N).levels := by
      cases hs : σ.sideAt N <;> simpa only [norm, hs] using hj
    have hne : up N j ≠ N := by dsimp [up]; split_ifs <;> omega
    have hh : up N j ∈ σ.levels ∧ up N j ≠ N ∧
        (erase σ N).extPositions j = σ.extPositions (up N j) ∧
        (erase σ N).sideAt j = σ.sideAt (up N j) ∧
        (erase σ N).maximumAt j = σ.maximumAt (up N j) :=
      ⟨(hLive σ N j hN hje).2.2, hne, hExt σ N j hN hje,
        hSide σ N j hN hje, hMaximum σ N j hN hje⟩
    cases hs : σ.sideAt N <;> simpa only [norm, hs] using hh
  refine ⟨hNormChild σ N, hNormDepth, hHistory,
    fun p q => hCaps σ N hN hterminal p q,
    fun fuel => hFuel fuel σ N hN hterminal, ?_⟩
  simpa only [bound, hNormChild] using hFuel (σ.childPositions.length+1) σ N hN hterminal

end ErdosSzekeres
