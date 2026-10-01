import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every fuel approximation and full bound of a uniform one-level root with an actual old marker and opposite global at most three are bounded by min(marker global,k-old maximum)-1. Absorb the old sibling maximum through closed normalization, retain all physical markers as positive inert barriers, and apply the closed small-global rank-region potential on the opposite axis. Works for arbitrary marker/run multiplicities, either side, no word-end conditions, and arbitrary natural globals/k/maximum. Supplies a join-sensitive upper for prospective neither-marked opposite-global-three selector; it does not prove the selector or larger-axis upper.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_one_level_root_bound_le_absorbed_marker_budget_of_small_opposite_global (A G k m : ℕ) (hA : A ≤ 3) (side : Ctx.Side) (word : List Ctx.Letter) (hletters : ∀ z ∈ word, z = Ctx.Letter.child ∨ z = Ctx.Letter.ext 1 side) (hmarker : Ctx.Letter.ext 1 side ∈ word) : let σ : Ctx.Context := { a := match side with | Ctx.Side.lower => A | Ctx.Side.upper => G, u := match side with | Ctx.Side.lower => G | Ctx.Side.upper => A, k := k, word := word, maxima := [m] }; (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ min G (k-m)-1) ∧ σ.bound ≤ min G (k-m)-1 := by
  classical
  have hShape (ρ : Context) (v : Side)
      (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v) :
      ∀ p j w, ρ.letterAt p = Letter.ext j w → j = 1 ∧ w = v := by
    intro p j w hext
    have hp : p < ρ.word.length := by
      by_contra hn
      have h := letterAt_of_length_le ρ (Nat.le_of_not_gt hn)
      rw [h] at hext
      cases hext
    have hget : ρ.word[p] = Letter.ext j w := by
      simpa [letterAt,hp] using hext
    have hmem : Letter.ext j w ∈ ρ.word := by
      rw [← hget]
      exact List.getElem_mem _
    rcases hw _ hmem with h | h
    · cases h
    · cases h
      exact ⟨rfl,rfl⟩
  have hSideOne (ρ : Context) (v : Side)
      (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v)
      (hx : ∃ x, x ∈ ρ.extPositions 1) : ρ.sideAt 1 = v := by
    cases hh : (ρ.extPositions 1).head? with
    | none =>
      obtain ⟨x,hx⟩ := hx
      have hn := List.head?_eq_none_iff.mp hh
      rw [hn] at hx
      exact False.elim (List.not_mem_nil hx)
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      cases he : ρ.letterAt p with
      | child => simp [extPositions,he] at hp
      | ext j w =>
        have hs := (hShape ρ v hw p j w he).2
        simp [sideAt,hh,he,hs]
  have hRootPositive (ρ : Context) (v : Side)
      (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v) :
      ∀ p j w, ρ.letterAt p = Letter.ext j w → 1 ≤ j := by
    intro p j w he
    have hj := (hShape ρ v hw p j w he).1
    omega
  let ρ : Context :=
    { a := match side with | Side.lower => A | Side.upper => G
      u := match side with | Side.lower => G | Side.upper => A
      k := k, word := word, maxima := [m] }
  let H := min G (k-m)
  let τ : Context :=
    { ρ with
      a := match side with | Side.lower => A | Side.upper => H
      u := match side with | Side.lower => H | Side.upper => A
      maxima := [] }
  let opp : Side → Side := fun v => match v with
    | Side.lower => Side.upper | Side.upper => Side.lower
  change (∀ fuel, boundFuel fuel ρ ≤ H-1) ∧ ρ.bound ≤ H-1
  obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp hmarker
  have hxl : x < ρ.word.length := (List.getElem?_eq_some_iff.mp hx).1
  have hletter : ρ.letterAt x = Letter.ext 1 side := by
    simp [letterAt,ρ,hx]
  have hExt : x ∈ ρ.extPositions 1 := by
    simp [extPositions,hxl,hletter]
  have hSide : ρ.sideAt 1 = side := hSideOne ρ side hletters ⟨x,hExt⟩
  have hN : 1 ∈ ρ.levels := by simp [levels,ρ]
  have hNorm :
      (∀ fuel, boundFuel fuel ρ ≤ boundFuel fuel τ) ∧ ρ.bound ≤ τ.bound := by
    have h := (ctx_sibling_maximum_upper_normalize ρ 1 hN).2
    cases side <;> simpa [hSide,ρ,τ,H,maximumAt] using h
  have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j :=
    hRootPositive τ side hletters
  have hNe : opp side ≠ side := by cases side <;> simp [opp]
  have hSmall :
      (match opp side with | Side.lower => τ.u | Side.upper => τ.a) ≤ 3 := by
    cases side <;> simpa [opp,τ] using hA
  have hRanks := ctx_small_global_axis_rank_region_potential τ hPositive
    (opp side) side hNe hSmall
  have hFuel (fuel : ℕ) : boundFuel fuel τ ≤ H-1 := by
    cases side <;> exact (hRanks.1 fuel).trans hRanks.2.2.1
  have hBound : τ.bound ≤ H-1 := by
    cases side <;> exact hRanks.2.1.trans hRanks.2.2.1
  exact ⟨fun fuel => (hNorm.1 fuel).trans (hFuel fuel),hNorm.2.trans hBound⟩

end ErdosSzekeres
