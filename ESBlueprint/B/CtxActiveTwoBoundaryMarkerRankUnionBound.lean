import ESBlueprint.B.CtxActiveBoundaryMarkerRankUnionBound
import ESBlueprint.B.CtxBoundLeInactivePruneCapacityThree
import ESBlueprint.B.CtxChainOneChildrenExteriorOfTwoLevels

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact opposite-rank union bound for a middle region bracketed by two positions of one indexed chosen level. All active children and younger same-axis markers lie between the positions, and min(global-2,k-maximum) is at most three. Every fuel approximation and the full bound are at most the original active opposite pure-rank union cardinality. Inactive children may lie anywhere; disconnected rank sets and older opposite histories are retained. The proof uses capacity-three inactive pruning, erases older chosen levels and applies two-boundary normalization. Supplies the linear middle-region component for the global-five quadratic marker route.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_active_two_boundary_marker_rank_union_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x y : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N) (hyBound : y ∈ σ.extPositions N)
  (hchildren : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p → x < p ∧ p < y)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    x < p ∧ p < y)
  (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
  (hsmall : min ((match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 2)
    (σ.k - σ.maximumAt N) ≤ 3) :
  let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := active.biUnion
    (fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card) ∧ σ.bound ≤ ranks.card := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let budget := (G σ t) - 1
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := active.biUnion
    (fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p))
  change (∀ fuel, boundFuel fuel σ ≤ ranks.card) ∧ σ.bound ≤ ranks.card
  have hAllChildren (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x y : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N) (hyBound : y ∈ σ.extPositions N)
  (hchildren : ∀ p ∈ σ.childPositions, x < p ∧ p < y)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    x < p ∧ p < y)
  (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
  (hsmall : min ((match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 2)
    (σ.k - σ.maximumAt N) ≤ 3)
  (S : Finset ℕ)
  (hRanks : ∀ p ∈ σ.childPositions,
    Finset.Icc (σ.leftExt t 0 p + 1)
      ((G σ t) - 1 - σ.rightExt t 0 p) ⊆ S) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ S.card) ∧ σ.bound ≤ S.card := by
    let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
    let letter (D L : ℕ) : Letter → Letter := fun x => match x with
      | Letter.child => Letter.child
      | Letter.ext j v => Letter.ext (idx D L j) v
    let erase (ρ : Context) (L : ℕ) : Context :=
      { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L-1) }
    let up (L j : ℕ) := if j < L then j else j+1
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
    have hUpZero (L : ℕ) (hL : 1 ≤ L) : up L 0 = 0 := by simp [up, show 0 < L by omega]
    have hSub (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side) (top : ℕ) :
        (((erase ρ L).levelsOn v top).map (up L)).Sublist (ρ.levelsOn v (up L top)) := by
      have hs : (((erase ρ L).levelsOn v top).map (up L)).Pairwise (· < ·) :=
        ((hSorted (erase ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
      have ho : (ρ.levelsOn v (up L top)).Pairwise (· < ·) := (hSorted ρ).filter _
      have hsubset : (((erase ρ L).levelsOn v top).map (up L)) ⊆ ρ.levelsOn v (up L top) := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        have hjl := (List.mem_filter.mp hj).1
        have hjc : (erase ρ L).sideAt j = v ∧ (top = 0 ∨ j < top) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        apply List.mem_filter.mpr
        refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
        apply decide_eq_true
        refine ⟨?_, ?_⟩
        · rw [← hSide ρ L j hL hjl]; exact hjc.1
        · rcases hjc.2 with rfl | hlt
          · exact Or.inl (hUpZero L (one_le_of_mem_levels hL))
          · exact Or.inr (hUpMono L j top hlt)
      have he : (ρ.levelsOn v (up L top)).filter
          (· ∈ (((erase ρ L).levelsOn v top).map (up L))) =
          (((erase ρ L).levelsOn v top).map (up L)) := by
        apply (ho.filter _).eq_of_mem_iff hs
        intro x
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨And.right, fun hx => ⟨hsubset hx, hx⟩⟩
      rw [← he]
      exact List.filter_sublist
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
    have hErasePositive (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
        (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) :
        ∀ p j v, (erase ρ L).letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      rw [hLetter] at hp
      have hL1 := one_le_of_mem_levels hL
      have hDepthPos : 1 ≤ ρ.maxima.length := by
        have h := (hLevelMem ρ L).mp hL
        omega
      cases he : ρ.letterAt p with
      | child =>
        simp only [he, letter] at hp
        cases hp
      | ext i w =>
        have hi := hPos p i w he
        simp only [he, letter] at hp
        have hij := (Letter.ext.inj hp).1
        dsimp only [idx] at hij
        split_ifs at hij <;> omega
    have hTerminal (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (N x y : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N) (hyBound : y ∈ σ.extPositions N)
    (hchildren : ∀ p ∈ σ.childPositions, x < p ∧ p < y)
    (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
      x < p ∧ p < y)
    (hterminal : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, j ≤ N)
    (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
    (hsmall : min ((match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 2)
      (σ.k - σ.maximumAt N) ≤ 3)
    (S : Finset ℕ)
    (hRanks : ∀ p ∈ σ.childPositions,
      Finset.Icc (σ.leftExt t 0 p + 1)
        ((G σ t) - 1 - σ.rightExt t 0 p) ⊆ S) :
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ S.card) ∧ σ.bound ≤ S.card := by
      let τ : Context := match σ.sideAt N with
        | Side.lower => { erase σ N with u := min (σ.u-2) (σ.k-σ.maximumAt N) }
        | Side.upper => { erase σ N with a := min (σ.a-2) (σ.k-σ.maximumAt N) }
      let P := (G σ t) - 1
      let active : Finset ℕ := τ.childPositions.toFinset.filter
        (fun p => 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p)
      let ranks := active.biUnion (fun p => Finset.Icc (τ.leftExt t 0 p + 1) (P - τ.rightExt t 0 p))
      have hNorm := ctx_two_boundary_marker_erase_normalize σ hpositive N x y hN hx hyBound hchildren hyounger hterminal
      have hNormFuel (fuel : ℕ) : boundFuel fuel σ ≤ boundFuel fuel τ := hNorm.2.1 fuel
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
        dsimp only [τ, P, G]
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
      have hSubset : ranks ⊆ S := by
        intro q hq
        obtain ⟨p, hp, hq⟩ := Finset.mem_biUnion.mp hq
        have hpChild : p ∈ τ.childPositions := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
        rw [hTauChild] at hpChild
        apply hRanks p hpChild
        simpa only [hPureLeft p, hPureRight p] using hq
      have hAll (fuel : ℕ) : boundFuel fuel σ ≤ S.card :=
        (hNormFuel fuel).trans ((hTauFuel fuel).trans (Finset.card_le_card hSubset))
      exact ⟨hAll, by simpa only [bound] using hAll (σ.childPositions.length + 1)⟩
    have hAll : ∀ D (ρ : Context), ρ.maxima.length = D →
        (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
        ∀ (N x y : ℕ), N ∈ ρ.levels → x ∈ ρ.extPositions N → y ∈ ρ.extPositions N →
        (∀ p ∈ ρ.childPositions, x < p ∧ p < y) →
        (∀ j ∈ ρ.levelsOn (ρ.sideAt N) N, ∀ p ∈ ρ.extPositions j,
          x < p ∧ p < y) →
        ∀ t : Side, ρ.sideAt N ≠ t →
        min ((match ρ.sideAt N with | Side.lower => ρ.u | Side.upper => ρ.a) - 2)
          (ρ.k - ρ.maximumAt N) ≤ 3 →
        ∀ S : Finset ℕ, (∀ p ∈ ρ.childPositions,
          Finset.Icc (ρ.leftExt t 0 p + 1)
            ((G ρ t) - 1 - ρ.rightExt t 0 p) ⊆ S) →
        ∀ fuel, boundFuel fuel ρ ≤ S.card := by
      intro D
      induction D using Nat.strong_induction_on with
      | h D ih =>
        intro ρ hD hPos N x y hN hx hyB hc hy t hne hsmall S hRanks
        by_cases hterminal : ∀ j ∈ ρ.levelsOn (ρ.sideAt N) 0, j ≤ N
        · exact (hTerminal ρ hPos N x y hN hx hyB hc hy hterminal
            t hne hsmall S hRanks).1
        · push Not at hterminal
          obtain ⟨L, hLOn, hNL⟩ := hterminal
          have hL : L ∈ ρ.levels := (List.mem_filter.mp hLOn).1
          have hLSide : ρ.sideAt L = ρ.sideAt N :=
            (of_decide_eq_true (List.mem_filter.mp hLOn).2).1
          have hLOpposite : ρ.sideAt L ≠ t := by simpa only [hLSide] using hne
          let τ := erase ρ L
          have hNMem := (hLevelMem ρ N).mp hN
          have hLMem := (hLevelMem ρ L).mp hL
          have hNτ : N ∈ τ.levels := by
            apply (hLevelMem τ N).mpr
            change 1 ≤ N ∧ N ≤ (erase ρ L).maxima.length
            rw [hDepth ρ L hL]
            omega
          have hupN : up L N = N := by simp only [up, if_pos hNL]
          have hSideN : τ.sideAt N = ρ.sideAt N := by
            rw [hSide ρ L N hL hNτ, hupN]
          have hMaximumN : τ.maximumAt N = ρ.maximumAt N := by
            rw [hMaximum ρ L N hL hNτ, hupN]
          have hxτ : x ∈ τ.extPositions N := by
            rw [hExt ρ L N hL hNτ, hupN]
            exact hx
          have hyBτ : y ∈ τ.extPositions N := by
            rw [hExt ρ L N hL hNτ, hupN]
            exact hyB
          have hChildτ : τ.childPositions = ρ.childPositions := hChild ρ L
          have hAτ : τ.a = ρ.a := rfl
          have hUτ : τ.u = ρ.u := rfl
          have hKτ : τ.k = ρ.k := rfl
          have hcτ : ∀ p ∈ τ.childPositions, x < p ∧ p < y := by
            simpa only [hChildτ] using hc
          have hyτ : ∀ j ∈ τ.levelsOn (τ.sideAt N) N, ∀ p ∈ τ.extPositions j,
              x < p ∧ p < y := by
            intro j hj p hp
            have hj' : j ∈ τ.levelsOn (ρ.sideAt N) N := by simpa only [hSideN] using hj
            have hjl : j ∈ τ.levels := (List.mem_filter.mp hj').1
            have hm := (hSub ρ L hL (ρ.sideAt N) N).subset (List.mem_map.mpr ⟨j, hj', rfl⟩)
            rw [hupN] at hm
            have hpOld : p ∈ ρ.extPositions (up L j) := by
              simpa only [τ, hExt ρ L j hL hjl] using hp
            exact hy (up L j) hm p hpOld
          have hneτ : τ.sideAt N ≠ t := by simpa only [hSideN] using hne
          have hsmallτ : min ((match τ.sideAt N with | Side.lower => τ.u | Side.upper => τ.a) - 2)
              (τ.k - τ.maximumAt N) ≤ 3 := by
            simpa only [hSideN, hMaximumN, hAτ, hUτ, hKτ] using hsmall
          have hRanksτ : ∀ p ∈ τ.childPositions,
              Finset.Icc (τ.leftExt t 0 p + 1)
                ((G τ t) - 1 - τ.rightExt t 0 p) ⊆ S := by
            intro p hp
            have hpOld : p ∈ ρ.childPositions := by simpa only [hChildτ] using hp
            simpa only [τ, hEraseLeft ρ L hL t hLOpposite p,
              hEraseRight ρ L hL t hLOpposite p] using hRanks p hpOld
          have hDepthLt : τ.maxima.length < D := by
            change (erase ρ L).maxima.length < D
            rw [hDepth ρ L hL, hD]
            rw [hD] at hLMem
            omega
          have hRec := ih τ.maxima.length hDepthLt τ rfl (hErasePositive ρ L hL hPos)
            N x y hNτ hxτ hyBτ hcτ hyτ t hneτ hsmallτ S hRanksτ
          have hMono := (ctx_erase_level_bound_mono ρ L hL).2.1
          intro fuel
          exact (hMono fuel).trans (hRec fuel)
    have h := hAll σ.maxima.length σ rfl hpositive N x y hN hx hyBound hchildren hyounger
      t hne hsmall S hRanks
    exact ⟨h, by simpa only [bound] using h (σ.childPositions.length + 1)⟩
  let prune (ρ : Context) (keep : List ℕ) (v : Side) : Context := { ρ with
    word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (ρ.maxima.length + 1) v
      | Letter.ext j s => Letter.ext j s) }
  have hPLen (ρ : Context) (keep : List ℕ) (v : Side) :
      (prune ρ keep v).word.length = ρ.word.length := by simp [prune]
  have hPLetter (ρ : Context) (keep : List ℕ) (v : Side) (p : ℕ) (hp : p < ρ.word.length) :
      (prune ρ keep v).letterAt p = (match ρ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (ρ.maxima.length + 1) v
      | Letter.ext j s => Letter.ext j s) := by
    simp only [prune, letterAt, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some]
  have hPChild (ρ : Context) (keep : List ℕ) (v : Side) :
      (prune ρ keep v).childPositions = ρ.childPositions.filter (· ∈ keep) := by
    simp only [childPositions, hPLen, List.filter_filter]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ keep v p (List.mem_range.mp hp)]
    cases ρ.letterAt p <;> simp
  have hPPos (ρ : Context) (keep : List ℕ) (v : Side)
      (hpos : ∀ p j s, ρ.letterAt p = Letter.ext j s → 1 ≤ j) :
      ∀ p j s, (prune ρ keep v).letterAt p = Letter.ext j s → 1 ≤ j := by
    intro p j s hp
    have hpl : p < ρ.word.length := by
      by_contra h
      have he := letterAt_of_length_le (prune ρ keep v)
        (show (prune ρ keep v).word.length ≤ p by rw [hPLen]; omega)
      rw [he] at hp
      cases hp
    rw [hPLetter ρ keep v p hpl] at hp
    cases he : ρ.letterAt p with
    | child =>
      by_cases hpk : p ∈ keep
      · simp [he, hpk] at hp
      · simp only [he, if_neg hpk, Letter.ext.injEq] at hp
        omega
    | ext i w =>
      have hi := hpos p i w he
      simp only [he, Letter.ext.injEq] at hp
      omega
  have hPExt (ρ : Context) (keep : List ℕ) (v : Side) (j : ℕ) (hj : j ∈ ρ.levels) :
      (prune ρ keep v).extPositions j = ρ.extPositions j := by
    have hjD : j ≤ ρ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range] at hj
      obtain ⟨i, hi, rfl⟩ := hj; omega
    simp only [extPositions, hPLen]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ keep v p (List.mem_range.mp hp)]
    cases ρ.letterAt p with
    | child => split_ifs <;> simp [show ρ.maxima.length + 1 ≠ j by omega]
    | ext i w => rfl
  have hPSide (ρ : Context) (keep : List ℕ) (v : Side) (j : ℕ) (hj : j ∈ ρ.levels) :
      (prune ρ keep v).sideAt j = ρ.sideAt j := by
    simp only [sideAt, hPExt ρ keep v j hj]
    cases hh : (ρ.extPositions j).head? with
    | none => rfl
    | some p =>
      have hp := List.mem_of_mem_head? hh
      have hpl := List.mem_range.mp (List.mem_filter.mp hp).1
      dsimp only
      rw [hPLetter ρ keep v p hpl]
      cases he : ρ.letterAt p with
      | child => simp [extPositions, he] at hp
      | ext i s => rfl
  have hPExtensions (ρ : Context) (keep : List ℕ) (v s : Side) (top x : ℕ) :
      (prune ρ keep v).leftExt s top x = ρ.leftExt s top x ∧
      (prune ρ keep v).rightExt s top x = ρ.rightExt s top x := by
    have hlevels (s : Side) (top : ℕ) :
        (prune ρ keep v).levelsOn s top = ρ.levelsOn s top := by
      change ρ.levels.filter _ = ρ.levels.filter _
      apply List.filter_congr
      intro j hj
      rw [hPSide ρ keep v j hj]
    have hfold : ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ ρ.levels) → ∀ z,
        ls.foldl (leftStep (prune ρ keep v)) z = ls.foldl (leftStep ρ) z ∧
        ls.foldl (rightStep (prune ρ keep v)) z = ls.foldl (rightStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro hj z
        have ht := ih (fun i hi => hj i (by simp [hi]))
        simp only [List.foldl_cons, leftStep, rightStep, hPExt ρ keep v j (hj j (by simp))]
        exact ⟨(ht _).1, (ht _).2⟩
    have hext (s : Side) (top x : ℕ) :
        (prune ρ keep v).leftExt s top x = ρ.leftExt s top x ∧
        (prune ρ keep v).rightExt s top x = ρ.rightExt s top x := by
      simp only [leftExt_eq, rightExt_eq, hlevels]
      constructor <;> congr 2 <;> apply List.map_congr_left <;> intro ls hls
      · exact congrArg Prod.snd (hfold ls
          (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) _).1
      · exact congrArg Prod.snd (hfold ls
          (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) _).2
    exact hext s top x
  have hPLimits (ρ : Context) (keep : List ℕ) (v : Side) (p q : ℕ) :
      (prune ρ keep v).cupLimit p q = ρ.cupLimit p q ∧
      (prune ρ keep v).capLimit p q = ρ.capLimit p q := by
    have hlevels (s : Side) (top : ℕ) :
        (prune ρ keep v).levelsOn s top = ρ.levelsOn s top := by
      change ρ.levels.filter _ = ρ.levels.filter _
      apply List.filter_congr
      intro j hj
      rw [hPSide ρ keep v j hj]
    have hext := hPExtensions ρ keep v
    have hchain (s : Side) : (prune ρ keep v).chainExt s p q = ρ.chainExt s p q := by
      simp only [chainExt, (hext s 0 p).1, (hext s 0 q).2]
    have hjoin (s : Side) : (prune ρ keep v).joinExt s p q = ρ.joinExt s p q := by
      simp only [joinExt, hchain, hlevels]
      congr 3
      apply List.map_congr_left
      intro j _
      simp only [(hext s j p).1, (hext s j q).2]
      rfl
    simp only [cupLimit, capLimit, hchain, hjoin]
    exact ⟨rfl, rfl⟩
  let s := σ.sideAt N
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [s]⟩
  have hOneLeft (p : ℕ) (hxp : x < p) : 1 ≤ σ.leftExt s 0 p := by
    have hm : x ∈ (σ.extPositions N).filter (· < p) := by simp [hx, hxp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (leftStep σ) (p, 0)).2))
      (List.mem_map.mpr ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
    change _ ≤ σ.leftExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (p : ℕ) (hpx : p < x) : 1 ≤ σ.rightExt s 0 p := by
    have hm : x ∈ (σ.extPositions N).filter (p < ·) := by simp [hx, hpx]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (rightStep σ) (p, 0)).2))
      (List.mem_map.mpr ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
    change _ ≤ σ.rightExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hChain (p : ℕ) (hp : p ∈ σ.childPositions) : 1 ≤ σ.chainExt s p p := by
    have hlet : σ.letterAt p = Letter.child := of_decide_eq_true (List.mem_filter.mp hp).2
    have hpx : p ≠ x := by
      intro heq
      subst p
      simp [extPositions, hlet] at hx
    rcases lt_or_gt_of_ne hpx with hpx | hxp
    · have hr := hOneRight p hpx
      simp only [chainExt]
      omega
    · have hl := hOneLeft p hxp
      simp only [chainExt]
      omega
  have hJoin (p : ℕ) : σ.maximumAt N ≤ σ.joinExt s p p := by
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).map
      (fun j => σ.leftExt s j p + σ.rightExt s j p + σ.maximumAt j))
      (List.mem_map.mpr ⟨N, hNOn, rfl⟩)
    unfold joinExt
    omega
  have hSmall (p : ℕ) (hp : p ∈ σ.childPositions) :
      min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
    have hc := hChain p hp
    have hj := hJoin p
    change min ((match s with | Side.lower => σ.u | Side.upper => σ.a) - 2)
      (σ.k - σ.maximumAt N) ≤ 3 at hsmall
    cases hs : s <;> simp only [hs] at hc hj hsmall
    · simp only [cupLimit, capLimit]
      omega
    · simp only [cupLimit, capLimit]
      omega
  let liveChildren := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let τ := prune σ liveChildren Side.lower
  have hτpositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j :=
    hPPos σ liveChildren Side.lower hpositive
  have hChild (p : ℕ) : p ∈ τ.childPositions ↔
      p ∈ σ.childPositions ∧ 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
    simp [τ, hPChild, liveChildren]
  have hSide : τ.sideAt N = σ.sideAt N := hPSide σ liveChildren Side.lower N hN
  have hNτ : N ∈ τ.levels := hN
  have hxτ : x ∈ τ.extPositions N := by
    simpa only [τ, hPExt σ liveChildren Side.lower N hN] using hx
  have hyBτ : y ∈ τ.extPositions N := by
    simpa only [τ, hPExt σ liveChildren Side.lower N hN] using hyBound
  have hLevels (v : Side) (top : ℕ) : τ.levelsOn v top = σ.levelsOn v top := by
    change σ.levels.filter _ = σ.levels.filter _
    apply List.filter_congr
    intro j hj
    rw [hPSide σ liveChildren Side.lower j hj]
  have hComparison := ctx_bound_le_inactive_prune_capacity_three σ hpositive hSmall
  have hChildrenτ : ∀ p ∈ τ.childPositions, x < p ∧ p < y := by
    intro p hp
    have hh := (hChild p).mp hp
    exact hchildren p hh.1 hh.2
  have hYoungerτ : ∀ j ∈ τ.levelsOn (τ.sideAt N) N, ∀ p ∈ τ.extPositions j,
      x < p ∧ p < y := by
    intro j hj p hp
    rw [hSide, hLevels] at hj
    have hjσ := (List.mem_filter.mp hj).1
    have hpσ : p ∈ σ.extPositions j := by
      simpa only [τ, hPExt σ liveChildren Side.lower j hjσ] using hp
    exact hyounger j hj p hpσ
  have hNormτ : min ((match τ.sideAt N with | Side.lower => τ.u | Side.upper => τ.a) - 2)
      (τ.k - τ.maximumAt N) ≤ 3 := by
    simpa only [hSide] using hsmall
  have hRanksτ : ∀ p ∈ τ.childPositions,
      Finset.Icc (τ.leftExt t 0 p + 1)
        ((G τ t) - 1 - τ.rightExt t 0 p) ⊆ ranks := by
    intro p hp q hq
    have hh := (hChild p).mp hp
    have hpa : p ∈ active := by simp [active, hh.1, hh.2.1, hh.2.2]
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpa, ?_⟩
    have hl := (hPExtensions σ liveChildren Side.lower t 0 p).1
    have hr := (hPExtensions σ liveChildren Side.lower t 0 p).2
    change (prune σ liveChildren Side.lower).leftExt t 0 p = _ at hl
    change (prune σ liveChildren Side.lower).rightExt t 0 p = _ at hr
    simpa only [τ, hl, hr, budget] using hq
  have ht : τ.sideAt N ≠ t := by rw [hSide]; exact hne
  have hb := (hAllChildren τ hτpositive N x y hNτ hxτ hyBτ hChildrenτ hYoungerτ
    t ht hNormτ ranks hRanksτ).2
  exact ⟨fun fuel => (hComparison.1 fuel).trans hb, hComparison.2.trans hb⟩

end ErdosSzekeres
