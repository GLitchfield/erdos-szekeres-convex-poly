import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxThinFourRankNextBandPotential
import ESBlueprint.B.CtxLargeChosenMaximumBracketedPartUnitBound
import ESBlueprint.B.CtxOldestAxisMaximumEraseNormalize
import ESBlueprint.B.CtxPartPruningHistoryTransport

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- The old large chosen maximum makes the bracketed chosen part unit. Normalize the opposite companion maximum while preserving the old chosen history and pure rank window, then apply the four-rank next-band bound. This pays the top-band cut budget 3k-8 without a coupling or source global-bound premise.
Positive labels, distinct axes, empty indexed opposite history, k at least five, and some indexed chosen maximum at least k-4.
All source-active pure chosen intervals have width at most two and lie inside one four-rank window.
A physical retained child and complementary physical children bracketing every retained source child; the new opposite maximum is at least one.
No bound on either source global parameter, no coupling or positivity restriction on the new chosen maximum, no active-retained or old-actual-occurrence premise, and no convexity, exact-depth or recursive potential premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_thin_four_rank_top_band_chosen_internal_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hclear : σ.levelsOn t 0 = []) (hk : 5 ≤ σ.k)
  (N : ℕ) (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s)
  (hmaximum : σ.k - 4 ≤ σ.maximumAt N)
  (L : ℕ)
  (hthin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤
      σ.leftExt s 0 p + 2)
  (hwindow : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    L ≤ σ.leftExt s 0 p + 1 ∧
      (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤ L + 3)
  (keep : List ℕ) (q₀ l r m n : ℕ)
  (hq₀ : q₀ ∈ σ.childPositions) (hqkeep : q₀ ∈ keep)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlnot : l ∉ keep) (hrnot : r ∉ keep)
  (hinside : ∀ p ∈ σ.childPositions, p ∈ keep → l < p ∧ p < r)
  (hn : 1 ≤ n) :
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
    Ctx.Context.boundFuel g (σ.part rest t n) ≤ 3 * σ.k - 8) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ 3 * σ.k - 8 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part keep s m
  let β := σ.part rest t n
  have hUnit := ctx_large_chosen_maximum_bracketed_part_unit_bound σ hpositive s N hN hNs
    hmaximum keep m l r hl hr hlnot hrnot hinside
  have hQ : q₀ ∈ β.extPositions 1 := by
    rw [part_extPositions_one hpositive]
    have hnot : q₀ ∉ rest := by simp [rest, hqkeep]
    exact List.mem_filter.mpr ⟨hq₀, by simp [hnot]⟩
  have hSide : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive rest t n hQ
  have hOne : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hTerminal : ∀ j ∈ β.levelsOn (β.sideAt 1) 0, j ≤ 1 := by
    rw [hSide, part_levelsOn_self_zero hSide, hclear]
    simp
  let f : Letter → Letter := fun z => match z with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext
        (if j = 1 then β.maxima.length else if 1 < j then j-1 else j) v
  let E : Context := {β with word := β.word.map f, maxima := β.maxima.eraseIdx 0}
  let ν : Context := match β.sideAt 1 with
    | Side.lower => {E with u := min β.u (β.k-β.maximumAt 1)}
    | Side.upper => {E with a := min β.a (β.k-β.maximumAt 1)}
  have hNorm := ctx_oldest_axis_maximum_erase_normalize β 1 hOne hTerminal
  have hToν : (∀ fuel, boundFuel fuel β ≤ boundFuel fuel ν) ∧ β.bound ≤ ν.bound :=
    ⟨hNorm.2.2.2.2.1, hNorm.2.2.2.2.2⟩
  let τ : Context := {σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ rest then Letter.child else Letter.ext (σ.maxima.length+1) t
      | Letter.ext j v => Letter.ext j v) }
  have hPrune := ctx_part_pruning_history_transport σ hpositive rest t n
  change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
    τ.childPositions = σ.childPositions.filter (· ∈ rest) ∧
    (∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧ τ.sideAt j = σ.sideAt j) ∧
    (∀ v top, τ.levelsOn v top = σ.levelsOn v top) ∧
    (∀ v top p, τ.leftExt v top p = σ.leftExt v top p ∧
      τ.rightExt v top p = σ.rightExt v top p) ∧
    (∀ p q, τ.cupLimit p q = σ.cupLimit p q ∧ τ.capLimit p q = σ.capLimit p q) ∧
    active τ = (active σ).filter (· ∈ rest) ∧
    (∀ fuel, boundFuel fuel β ≤ boundFuel fuel τ) ∧ β.bound ≤ τ.bound at hPrune
  obtain ⟨hτPos, hτChild, hτHist, hτLevels, hτExt, hτLimits, hτActive, _, _⟩ := hPrune
  have hWord : β.word.map f = τ.word := by
    change ((List.range σ.word.length).map _).map f = (List.range σ.word.length).map _
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    cases he : σ.letterAt p with
    | child =>
      dsimp only [Function.comp_def]
      rw [he]
      by_cases hk : p ∈ rest
      · simp only [if_pos hk, f]
      · simp only [if_neg hk, f, if_pos rfl]
        rfl
    | ext j v =>
      have hj := hpositive p j v he
      dsimp only [Function.comp_def]
      rw [he]
      simp only [f, show j+1 ≠ 1 by omega, if_false, show 1 < j+1 by omega,
        if_true, Nat.add_sub_cancel]
  have hMaximum : β.maximumAt 1 = n := part_maximumAt_one σ rest t n
  have hνEq : ν = (match t with
      | Side.lower => {τ with u := min σ.u (σ.k-n)}
      | Side.upper => {τ with a := min σ.a (σ.k-n)}) := by
    cases t <;> simp only [ν, hSide, E, hWord, hMaximum]
    all_goals rfl
  have hνPos : ∀ p j v, ν.letterAt p = Letter.ext j v → 1 ≤ j := by
    cases t <;> rw [hνEq] <;> exact hτPos
  have hνChild : ν.childPositions = τ.childPositions := by cases t <;> rw [hνEq] <;> rfl
  have hνExt (v : Side) (p : ℕ) : ν.leftExt v 0 p = σ.leftExt v 0 p ∧
      ν.rightExt v 0 p = σ.rightExt v 0 p := by
    have he : ν.leftExt v 0 p = τ.leftExt v 0 p ∧ ν.rightExt v 0 p = τ.rightExt v 0 p := by
      cases t <;> rw [hνEq] <;> exact ⟨rfl, rfl⟩
    exact ⟨he.1.trans (hτExt v 0 p).1, he.2.trans (hτExt v 0 p).2⟩
  have hChosen : G ν s = G σ s := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · rw [hνEq] <;> rfl
    · rw [hνEq] <;> rfl
    · exact False.elim (hne rfl)
  have hOpposite : G ν t ≤ σ.k-n := by
    cases t <;> rw [hνEq]
    all_goals exact Nat.min_le_right _ _
  have hνLimits (p : ℕ) : ν.cupLimit p p ≤ τ.cupLimit p p ∧ ν.capLimit p p ≤ τ.capLimit p p := by
    cases t <;> rw [hνEq]
    · refine ⟨?_, le_rfl⟩
      exact min_le_min (Nat.sub_le_sub_right (Nat.sub_le_sub_right (Nat.min_le_left _ _) 1) _) le_rfl
    · refine ⟨le_rfl, ?_⟩
      exact min_le_min (Nat.sub_le_sub_right (Nat.sub_le_sub_right (Nat.min_le_left _ _) 1) _) le_rfl
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by simp [active]
  have hSource (p : ℕ) (hp : p ∈ active ν) : p ∈ active σ := by
    have hh := (hActive ν p).mp hp
    have hle := hνLimits p
    have hτ : p ∈ active τ := (hActive τ p).mpr ⟨by rw [← hνChild]; exact hh.1, by omega, by omega⟩
    rw [hτActive] at hτ
    exact (Finset.mem_filter.mp hτ).1
  have hThinν : ∀ p ∈ ν.childPositions, 0 < ν.cupLimit p p → 0 < ν.capLimit p p →
      G ν s-1-ν.rightExt s 0 p ≤ ν.leftExt s 0 p+2 := by
    intro p hp hcu hca
    have hh := (hActive σ p).mp (hSource p ((hActive ν p).mpr ⟨hp,hcu,hca⟩))
    rw [hChosen, (hνExt s p).1, (hνExt s p).2]
    cases s <;> exact hthin p hh.1 hh.2.1 hh.2.2
  have hνK : ν.k = σ.k := by cases t <;> rw [hνEq] <;> rfl
  have hνLevels : ν.levels = σ.levels := by cases t <;> rw [hνEq] <;> rfl
  have hνN : N ∈ ν.levels := by rw [hνLevels]; exact hN
  have hνSideN : ν.sideAt N = s := by
    have hh : ν.sideAt N = τ.sideAt N := by cases t <;> rw [hνEq] <;> rfl
    exact hh.trans ((hτHist N hN).2.trans hNs)
  have hνMaxN : ν.maximumAt N = σ.maximumAt N := by cases t <;> rw [hνEq] <;> rfl
  have hνClear : ν.levelsOn t 0 = [] := by
    have hh : ν.levelsOn t 0 = τ.levelsOn t 0 := by cases t <;> rw [hνEq] <;> rfl
    exact hh.trans ((hτLevels t 0).trans hclear)
  have hνOpp : G ν t ≤ ν.k - 1 := by rw [hνK]; omega
  have hWindowν : ∀ p ∈ ν.childPositions, 0 < ν.cupLimit p p → 0 < ν.capLimit p p →
      L ≤ ν.leftExt s 0 p + 1 ∧ G ν s-1-ν.rightExt s 0 p ≤ L+3 := by
    intro p hp hcu hca
    have hh := (hActive σ p).mp (hSource p ((hActive ν p).mpr ⟨hp,hcu,hca⟩))
    rw [hChosen, (hνExt s p).1, (hνExt s p).2]
    cases s <;> exact hwindow p hh.1 hh.2.1 hh.2.2
  have hOtherν := ctx_thin_four_rank_next_band_potential ν hνPos s t hne hνClear
    (by cases t <;> exact hνOpp) (by rw [hνK]; exact hk) N hνN hνSideN
    (by rw [hνK, hνMaxN]; exact hmaximum) L
    (by cases s <;> exact hThinν) (by cases s <;> exact hWindowν)
  have hOther : (∀ fuel, boundFuel fuel β ≤ 3*σ.k-9) ∧ β.bound ≤ 3*σ.k-9 := by
    have hh : (∀ fuel, boundFuel fuel ν ≤ 3*σ.k-9) ∧ ν.bound ≤ 3*σ.k-9 := by
      simpa only [hνK] using hOtherν
    exact ⟨fun fuel => (hToν.1 fuel).trans (hh.1 fuel), hToν.2.trans hh.2⟩
  have hBudget : 1+(3*σ.k-9) ≤ 3*σ.k-8 := by omega
  exact ⟨fun f g => (Nat.add_le_add (hUnit.1 f) (hOther.1 g)).trans hBudget,
    (Nat.add_le_add hUnit.2 hOther.2).trans hBudget⟩


end ErdosSzekeres
