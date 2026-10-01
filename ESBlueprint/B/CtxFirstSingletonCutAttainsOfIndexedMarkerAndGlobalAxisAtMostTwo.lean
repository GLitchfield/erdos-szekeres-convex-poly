import ESBlueprint.B.CtxBoundLeSumPointBases

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- The first global child singleton cut attains whenever an arbitrary raw context has an actual indexed marker on a global axis at most two, k at least three and at least two child runs. Return the first-child head and membership, legal explicit singleton maximum one, raw singleton threshold and opposite complementary maximum k-1-1. Reuse the unconditional indexed-marker zero-bound argument; the cut value is nonnegative. No positive labels, WellFormed, legal globals, sibling maxima or uniform-word assumptions. Supplies the marker-global-at-most-two N_ends edge after root specialization; marker-free opposite-global-two and full selector remain open.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_first_singleton_cut_attains_of_indexed_marker_and_global_axis_at_most_two (σ : Ctx.Context) (s : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels) (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 2) (hk : 3 ≤ σ.k) : let opposite : Ctx.Side := match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower; 2 ≤ σ.numRuns → ∃ p : ℕ, σ.childPositions.head? = some p ∧ p ∈ σ.childPositions ∧ 1 ≤ σ.k-2 ∧ σ.bound ≤ decomposableThreshold ((σ.part [p] s 1).capLimit p p+1) ((σ.part [p] s 1).cupLimit p p+1) σ.k + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) opposite (σ.k-1-1)).bound := by
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
    have hpx : p ≠ x := by
      intro he
      subst x
      have hc := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := (List.mem_filter.mp hx).2
      simp [hc] at he
    have hChain : 1 ≤ σ.chainExt s p p := by
      by_cases h : p < x
      · have hright := hOneRight σ s N p x hNOn hx h
        unfold chainExt
        omega
      · have hleft := hOneLeft σ s N p x hNOn hx (by omega)
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
  change 2 ≤ σ.numRuns → _
  intro hRuns
  have hlen := numRuns_le_length σ
  cases hcp : σ.childPositions with
  | nil =>
    rw [hcp] at hlen
    simp only [List.length_nil] at hlen
    omega
  | cons p ps =>
    refine ⟨p,rfl,by simp,by omega,?_⟩
    rw [hBound]
    exact Nat.zero_le _

end ErdosSzekeres
