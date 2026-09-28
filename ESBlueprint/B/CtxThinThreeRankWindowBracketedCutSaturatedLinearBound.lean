import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxLargeChosenMaximumBracketedPartUnitBound
import ESBlueprint.B.CtxOldestAxisMaximumEraseNormalize
import ESBlueprint.B.CtxPartPruningHistoryTransport
import ESBlueprint.B.CtxThinRankRectangleContextCoverPotential

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Bound both fuel approximations and the full cut sum by 2*k-4 for an internally bracketed chosen part. The source has empty indexed opposite history, an indexed chosen maximum at least k-4, and every active pure chosen interval has at most two ranks inside a common window of three consecutive ranks. Positive coupled sibling maxima sum to k-1. There is no source global-cap restriction, chosen-history depth or occurrence restriction, convexity requirement, or recursive potential premise. The large original maximum makes the chosen part unit; normalize the opposite companion while preserving chosen rank traces, and pay its thin-rectangle cover from the coupled maximum. This removes the chosen-internal-cut case in the prospective three-rank saturation saving; the other geometries remain open.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_thin_three_rank_window_bracketed_cut_saturated_linear_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hclear : σ.levelsOn t 0 = [])
  (N : ℕ) (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s)
  (hmaximum : σ.k - 4 ≤ σ.maximumAt N)
  (L : ℕ)
  (hthin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤
      σ.leftExt s 0 p + 2)
  (hwindow : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    L ≤ σ.leftExt s 0 p + 1 ∧
      (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤ L + 2)
  (keep : List ℕ) (q₀ l r m n : ℕ)
  (hq₀ : q₀ ∈ σ.childPositions) (hqkeep : q₀ ∈ keep)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlnot : l ∉ keep) (hrnot : r ∉ keep)
  (hinside : ∀ p ∈ σ.childPositions, p ∈ keep → l < p ∧ p < r)
  (hm : 1 ≤ m) (hn : 1 ≤ n) (hsum : m + n = σ.k - 1) :
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
    Ctx.Context.boundFuel g (σ.part rest t n) ≤ 2 * σ.k - 4) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ 2 * σ.k - 4 := by
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
    · rw [hνEq]
    · rw [hνEq]
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
    have ht := hthin p hh.1 hh.2.1 hh.2.2
    cases s <;> exact ht
  let ranks (v : Side) (p : ℕ) := Finset.Icc (ν.leftExt v 0 p+1) (G ν v-1-ν.rightExt v 0 p)
  let cost (I : Finset ℕ) := if I=∅ then 0 else
    ((I.biUnion (ranks s)).card-1)*((I.biUnion (ranks t)).card-1)+1
  have hCover := ctx_thin_rank_rectangle_context_cover_potential ν hνPos s t hne
    (by cases s <;> exact hThinν) [active ν]
    (fun p hp => ⟨active ν, by simp, hp⟩)
    (by intro I hI; have he := List.mem_singleton.mp hI; subst I; exact Finset.Subset.refl _)
  change (∀ fuel, boundFuel fuel ν ≤ ([active ν].map cost).sum) ∧
    ν.bound ≤ ([active ν].map cost).sum at hCover
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hCover
  have hRankX : (active ν).biUnion (ranks s) ⊆ Finset.Icc L (L+2) := by
    intro z hz
    obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
    have hh := (hActive σ p).mp (hSource p hp)
    have hw := hwindow p hh.1 hh.2.1 hh.2.2
    have hzz := Finset.mem_Icc.mp hz
    rw [hChosen, (hνExt s p).1, (hνExt s p).2] at hzz
    cases s <;> simp only [G] at hw hzz <;> exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hRankY : (active ν).biUnion (ranks t) ⊆ Finset.Icc 1 m := by
    intro z hz
    obtain ⟨p,_,hz⟩ := Finset.mem_biUnion.mp hz
    have hh := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hXCard : ((active ν).biUnion (ranks s)).card ≤ 3 := by
    have hh := Finset.card_le_card hRankX
    simpa only [Nat.card_Icc, show L+2+1-L=3 by omega] using hh
  have hYCard : ((active ν).biUnion (ranks t)).card ≤ m := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hRankY
  have hCost : cost (active ν) ≤ 2*m-1 := by
    by_cases he : active ν=∅
    · simp only [cost, if_pos he]; omega
    have hh := Nat.mul_le_mul (show ((active ν).biUnion (ranks s)).card-1 ≤ 2 by omega)
      (show ((active ν).biUnion (ranks t)).card-1 ≤ m-1 by omega)
    simp only [cost, if_neg he]
    omega
  have hOther : (∀ fuel, boundFuel fuel β ≤ 2*m-1) ∧ β.bound ≤ 2*m-1 :=
    ⟨fun fuel => (hToν.1 fuel).trans ((hCover.1 fuel).trans hCost), hToν.2.trans (hCover.2.trans hCost)⟩
  have hBudget : 1+(2*m-1) ≤ 2*σ.k-4 := by omega
  exact ⟨fun f g => (Nat.add_le_add (hUnit.1 f) (hOther.1 g)).trans hBudget,
    (Nat.add_le_add hUnit.2 hOther.2).trans hBudget⟩


end ErdosSzekeres
