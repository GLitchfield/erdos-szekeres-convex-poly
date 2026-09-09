import ESBlueprint.B.CtxBoundaryMarkerEraseNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A full-history opposite-rank budget after absorbing the oldest indexed boundary marker on its own axis. When the normalized marker-side global parameter is at most three, subtract uniform left and right opposite-axis extension bounds from the entire original history, including older opposite levels, from the opposite global budget. Bounds every fuel approximation and the full recursive bound. Covers positive labels, repeated markers, arbitrary maxima, empty children and both axes/directions. Uses boundary erasure normalization to retain the older opposite constraints discarded by truncation, supplying a sharper companion contribution in the singleton-end sandwich obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_boundary_marker_full_rank_budget (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
  (rightward : Bool)
  (hchildren : ∀ p ∈ σ.childPositions, if rightward then p < x else x < p)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    if rightward then p < x else x < p)
  (hterminal : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, j ≤ N)
  (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
  (hsmall : min ((match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
    (σ.k - σ.maximumAt N) ≤ 3)
  (A B : ℕ)
  (hLeft : ∀ p ∈ σ.childPositions, A ≤ σ.leftExt t 0 p)
  (hRight : ∀ p ∈ σ.childPositions, B ≤ σ.rightExt t 0 p) :
  let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ budget) ∧ σ.bound ≤ budget := by
  classical
  let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
  let letter (D L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext (idx D L j) v
  let erase (ρ : Context) (L : ℕ) : Context :=
    { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L-1) }
  let up (L j : ℕ) := if j < L then j else j+1
  let τ : Context := match σ.sideAt N with
    | Side.lower => { erase σ N with u := min (σ.u-1) (σ.k-σ.maximumAt N) }
    | Side.upper => { erase σ N with a := min (σ.a-1) (σ.k-σ.maximumAt N) }
  let P := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let active : Finset ℕ := τ.childPositions.toFinset.filter
    (fun p => 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p)
  let ranks := active.biUnion (fun p => Finset.Icc (τ.leftExt t 0 p + 1) (P - τ.rightExt t 0 p))
  change (∀ fuel, boundFuel fuel σ ≤ P - A - B) ∧ σ.bound ≤ P - A - B
  have hNorm := ctx_boundary_marker_erase_normalize σ hpositive N x hN hx rightward hchildren hyounger hterminal
  have hNormFuel (fuel : ℕ) : boundFuel fuel σ ≤ boundFuel fuel τ := hNorm.2.1 fuel
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
  have hUpMono (L i j : ℕ) (h : i < j) : up L i < up L j := by
    dsimp [up]; split_ifs <;> omega
  have hFoldLeft (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase ρ L).levels) → ∀ z,
      ls.foldl (leftStep (erase ρ L)) z = (ls.map (up L)).foldl (leftStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, leftStep, hExt ρ L j hL (hj j (by simp))]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hFoldRight (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase ρ L).levels) → ∀ z,
      ls.foldl (rightStep (erase ρ L)) z = (ls.map (up L)).foldl (rightStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, rightStep, hExt ρ L j hL (hj j (by simp))]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hOppLevels (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (v : Side) (hne : ρ.sideAt L ≠ v) :
      ((erase ρ L).levelsOn v 0).map (up L) = ρ.levelsOn v 0 := by
    have hs : (((erase ρ L).levelsOn v 0).map (up L)).Pairwise (· < ·) :=
      ((hSorted (erase ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
    apply hs.eq_of_mem_iff ((hSorted ρ).filter _)
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hjl := (List.mem_filter.mp hj).1
      have hjc : (erase ρ L).sideAt j = v ∧ (0 = 0 ∨ j < 0) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      apply List.mem_filter.mpr
      refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
      rw [hSide ρ L j hL hjl] at hjc
      apply decide_eq_true
      exact ⟨hjc.1, Or.inl rfl⟩
    · intro hi
      have hil := (hLevelMem ρ i).mp (List.mem_filter.mp hi).1
      have hic : ρ.sideAt i = v ∧ (0 = 0 ∨ i < 0) :=
        of_decide_eq_true (List.mem_filter.mp hi).2
      have hiL : i ≠ L := by intro h; subst i; exact hne hic.1
      have hLL := (hLevelMem ρ L).mp hL
      let j := if i < L then i else i-1
      have hup : up L j = i := by dsimp [up, j]; split_ifs <;> omega
      have hjl : j ∈ (erase ρ L).levels := by
        apply (hLevelMem (erase ρ L) j).mpr
        rw [hDepth ρ L hL]
        dsimp [j]
        split_ifs <;> omega
      apply List.mem_map.mpr
      refine ⟨j, ?_, hup⟩
      apply List.mem_filter.mpr
      refine ⟨hjl, ?_⟩
      apply decide_eq_true
      rw [hSide ρ L j hL hjl, hup]
      exact ⟨hic.1, Or.inl rfl⟩
  have hEraseLeft (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (v : Side) (hne : ρ.sideAt L ≠ v) (p : ℕ) :
      (erase ρ L).leftExt v 0 p = ρ.leftExt v 0 p := by
    rw [leftExt_eq, leftExt_eq, ← hOppLevels ρ L hL v hne, List.sublists_map, List.map_map]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    have hl : ∀ j ∈ ls, j ∈ (erase ρ L).levels :=
      fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1
    exact congrArg Prod.snd (hFoldLeft ρ L hL ls hl (p,0))
  have hEraseRight (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (v : Side) (hne : ρ.sideAt L ≠ v) (p : ℕ) :
      (erase ρ L).rightExt v 0 p = ρ.rightExt v 0 p := by
    rw [rightExt_eq, rightExt_eq, ← hOppLevels ρ L hL v hne, List.sublists_map, List.map_map]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    have hl : ∀ j ∈ ls, j ∈ (erase ρ L).levels :=
      fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1
    exact congrArg Prod.snd (hFoldRight ρ L hL ls hl (p,0))
  have hPureLeft (p : ℕ) : τ.leftExt t 0 p = σ.leftExt t 0 p := by
    cases hs : σ.sideAt N <;> simpa only [τ, hs] using hEraseLeft σ N hN t hne p
  have hPureRight (p : ℕ) : τ.rightExt t 0 p = σ.rightExt t 0 p := by
    cases hs : σ.sideAt N <;> simpa only [τ, hs] using hEraseRight σ N hN t hne p
  have hTauLetter (p : ℕ) : τ.letterAt p = letter σ.maxima.length N (σ.letterAt p) := by
    cases hs : σ.sideAt N <;> simpa only [τ, hs] using hLetter σ N p
  have hTauChild : τ.childPositions = σ.childPositions := by
    cases hs : σ.sideAt N <;> simpa only [τ, hs] using hChild σ N
  have hN1 : 1 ≤ N := one_le_of_mem_levels hN
  have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    rw [hTauLetter] at hp
    cases he : σ.letterAt p with
    | child =>
      simp only [he, letter] at hp
      cases hp
    | ext i w =>
      have hi := hpositive p i w he
      simp only [he, letter] at hp
      have hij := (Letter.ext.inj hp).1
      have hDepthPos : 1 ≤ σ.maxima.length := by
        have h := (hLevelMem σ N).mp hN
        omega
      dsimp only [idx] at hij
      split_ifs at hij <;> omega
  have hSmall : (match σ.sideAt N with | Side.lower => τ.u | Side.upper => τ.a) ≤ 3 := by
    cases hs : σ.sideAt N <;> simpa only [τ, hs] using hsmall
  have hBudget : (fun v : Side => match v with | Side.lower => τ.u - 1 | Side.upper => τ.a - 1) t = P := by
    dsimp only [τ, P]
    cases hs : σ.sideAt N <;> cases ht : t <;> simp_all only [ne_eq, not_true_eq_false] <;> rfl
  have hPotential := ctx_small_global_axis_rank_region_potential τ hPositive (σ.sideAt N) t hne hSmall
  have hTauFuel (fuel : ℕ) : boundFuel fuel τ ≤ ranks.card := by
    have h := hPotential.1 fuel
    dsimp only at h hBudget
    split_ifs at h
    · cases ht : t <;> simp only [ht] at h hBudget <;>
        simpa only [ranks, active, ht, hBudget] using h
    · have h' := h.trans (Nat.min_le_right _ _)
      cases ht : t <;> simp only [ht] at h' hBudget <;>
        simpa only [ranks, active, ht, hBudget] using h'
  have hSubset : ranks ⊆ Finset.Icc (A + 1) (P - B) := by
    intro r hr
    obtain ⟨p, hp, hr⟩ := Finset.mem_biUnion.mp hr
    have hpChild : p ∈ τ.childPositions := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    rw [hTauChild] at hpChild
    have hl := hLeft p hpChild
    have hr' := hRight p hpChild
    rw [← hPureLeft p] at hl
    rw [← hPureRight p] at hr'
    have hI := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hCard : ranks.card ≤ P - A - B := by
    calc
      ranks.card ≤ (Finset.Icc (A + 1) (P - B)).card := Finset.card_le_card hSubset
      _ = P - A - B := by rw [Nat.card_Icc]; omega
  have hAll (fuel : ℕ) : boundFuel fuel σ ≤ P - A - B :=
    (hNormFuel fuel).trans ((hTauFuel fuel).trans hCard)
  exact ⟨hAll, by simpa only [bound] using hAll (σ.childPositions.length + 1)⟩

end ErdosSzekeres
