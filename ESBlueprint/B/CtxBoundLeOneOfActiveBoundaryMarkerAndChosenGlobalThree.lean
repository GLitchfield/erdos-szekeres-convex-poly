import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank

set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

namespace ErdosSzekeres
open Ctx Ctx.Context

/-- Raw every-fuel and full-bound upper one whenever a chosen global axis is at most three and all active genuine children lie on one side of an actual indexed same-axis boundary marker. Exports no well-formedness, maximum legality, younger-marker orientation, uniform-word, run-count, or opposite-global assumptions. Uses indexed singleton left/right witnesses to give the common active singleton rank, rather than incorrectly equating capacity one with common rank.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_bound_le_one_of_active_boundary_marker_and_chosen_global_three (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels)
    (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
    (hglobal : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3)
    (rightward : Bool)
    (hboundary : ∀ p ∈ σ.childPositions,
      0 < σ.cupLimit p p → 0 < σ.capLimit p p →
      if rightward then p < x else x < p) :
    (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ 1) ∧ σ.bound ≤ 1 := by
  classical
  have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq,hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
      (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons,List.foldl_nil,leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq,hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
      (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons,List.foldl_nil,rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hs]⟩
  let rank : ℕ := if rightward then 1 else 2
  have hRank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
      σ.leftExt s 0 p + 1 = rank ∧ rank + σ.rightExt s 0 p =
        (match s with | Ctx.Side.lower => σ.u - 1 | Ctx.Side.upper => σ.a - 1) := by
    intro p hp hcup hcap
    have hSide := hboundary p hp hcup hcap
    cases rightward with
    | false =>
      have hxp : x < p := by simpa using hSide
      have hleft := hOneLeft σ s N p x hNOn hx hxp
      cases s with
      | lower =>
        change σ.leftExt Ctx.Side.lower 0 p + 1 = 2 ∧
          2 + σ.rightExt Ctx.Side.lower 0 p = σ.u - 1
        simp only [Ctx.Context.cupLimit, Ctx.Context.chainExt] at hcup
        dsimp only at hglobal
        omega
      | upper =>
        change σ.leftExt Ctx.Side.upper 0 p + 1 = 2 ∧
          2 + σ.rightExt Ctx.Side.upper 0 p = σ.a - 1
        simp only [Ctx.Context.capLimit, Ctx.Context.chainExt] at hcap
        dsimp only at hglobal
        omega
    | true =>
      have hpx : p < x := by simpa using hSide
      have hright := hOneRight σ s N p x hNOn hx hpx
      cases s with
      | lower =>
        change σ.leftExt Ctx.Side.lower 0 p + 1 = 1 ∧
          1 + σ.rightExt Ctx.Side.lower 0 p = σ.u - 1
        simp only [Ctx.Context.cupLimit, Ctx.Context.chainExt] at hcup
        dsimp only at hglobal
        omega
      | upper =>
        change σ.leftExt Ctx.Side.upper 0 p + 1 = 1 ∧
          1 + σ.rightExt Ctx.Side.upper 0 p = σ.a - 1
        simp only [Ctx.Context.capLimit, Ctx.Context.chainExt] at hcap
        dsimp only at hglobal
        omega
  cases s with
  | lower =>
    have hCommon := ctx_bound_le_one_of_common_singleton_rank σ hpositive Ctx.Side.lower rank hRank
    exact ⟨hCommon.1, hCommon.2.1⟩
  | upper =>
    have hCommon := ctx_bound_le_one_of_common_singleton_rank σ hpositive Ctx.Side.upper rank hRank
    exact ⟨hCommon.1, hCommon.2.1⟩

end ErdosSzekeres
