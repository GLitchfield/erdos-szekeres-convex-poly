import ESBlueprint.B.CtxBoundLeSumPointBases
import ESBlueprint.B.CtxBoundAttainedByEndCut

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every fuel approximation and full bound vanish for an arbitrary raw context when two actual indexed chosen-side markers bracket every child and the chosen global is at most three. Each child has a chosen marker on both sides, so chosen chain extension is at least two and chosen point limit zero. No opposite global, positivity, WellFormed, legal k, maxima, run count or history hypotheses. Uses raw sum-point-base domination and fuel stabilization; closes the both-marked chosen-three degeneracy for arbitrary opposite axis.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_bound_zero_of_bracketed_children_and_indexed_chosen_global_three (σ : Ctx.Context) (s : Ctx.Side) (N x y : ℕ) (hN : N ∈ σ.levels) (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions N) (hbracket : ∀ p ∈ σ.childPositions, x < p ∧ p < y) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 3) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ = 0) ∧ σ.bound = 0 := by
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
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN,by simp [hs]⟩
  have hPoint : ∀ p ∈ σ.childPositions,
      baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k = 0 := by
    intro p hp
    have hleft := hOneLeft σ s N p x hNOn hx (hbracket p hp).1
    have hright := hOneRight σ s N p y hNOn hy (hbracket p hp).2
    have hChain : 2 ≤ σ.chainExt s p p := by
      unfold chainExt
      omega
    cases s with
    | lower =>
      dsimp only at hglobal
      have hzero : σ.cupLimit p p = 0 := by
        simp only [cupLimit]
        omega
      simp [baseOf,hzero]
    | upper =>
      dsimp only at hglobal
      have hzero : σ.capLimit p p = 0 := by
        simp only [capLimit]
        omega
      simp [baseOf,hzero]
  have hMap :
      σ.childPositions.map (fun p => baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k) =
        σ.childPositions.map (fun _ => 0) := by
    apply List.map_congr_left
    intro p hp
    exact hPoint p hp
  have hBound : σ.bound = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa only [hMap,List.sum_map_zero] using ctx_bound_le_sum_point_bases σ
  have hFuel (fuel : ℕ) : boundFuel fuel σ = 0 := by
    have hle : boundFuel fuel σ ≤ σ.bound := by
      by_cases hf : σ.childPositions.length+1 ≤ fuel
      · exact (boundFuel_eq_bound σ hf).le
      · exact boundFuel_mono (by omega : fuel ≤ σ.childPositions.length+1) σ
    rw [hBound] at hle
    exact Nat.eq_zero_of_le_zero hle
  exact ⟨hFuel,hBound⟩

end ErdosSzekeres
