import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- An actual marker on the rank axis removes the lower extreme rank from every child interval to its right and the upper extreme rank from every child interval to its left. This exports the synthetic companion marker endpoint loss isolated by the bounded mixed-overlap falsifier.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_actual_marker_opposite_rank_interval_endpoint_exclusion (σ : Ctx.Context) (t : Ctx.Side) (N x p : ℕ) (hN : N ∈ σ.levels) (hNt : σ.sideAt N = t) (hx : x ∈ σ.extPositions N) (hp : p ∈ σ.childPositions) : let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; let interval := Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p); (x < p ∧ ∀ r ∈ interval, 2 ≤ r) ∨ (p < x ∧ ∀ r ∈ interval, r + 2 ≤ global) := by
  classical
  let G := match t, hNt with
    | Side.lower, _ => σ.u
    | Side.upper, _ => σ.a
  let I := Finset.Icc (σ.leftExt t 0 p + 1)
    (G - 1 - σ.rightExt t 0 p)
  change (x < p ∧ ∀ r ∈ I, 2 ≤ r) ∨
    (p < x ∧ ∀ r ∈ I, r + 2 ≤ G)
  have hOneLeft (j q z : ℕ) (hj : j ∈ σ.levelsOn t 0)
      (hz : z ∈ σ.extPositions j) (hzq : z < q) :
      1 ≤ σ.leftExt t 0 q := by
    have hm : z ∈ (σ.extPositions j).filter (· < q) := by simp [hz, hzq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn t 0).sublists.map
      (fun ls => (ls.foldl (leftStep σ) (q, 0)).2))
      (List.mem_map.mpr ⟨[j],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ σ.leftExt t 0 q at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (j q z : ℕ) (hj : j ∈ σ.levelsOn t 0)
      (hz : z ∈ σ.extPositions j) (hqz : q < z) :
      1 ≤ σ.rightExt t 0 q := by
    have hm : z ∈ (σ.extPositions j).filter (q < ·) := by simp [hz, hqz]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn t 0).sublists.map
      (fun ls => (ls.foldl (rightStep σ) (q, 0)).2))
      (List.mem_map.mpr ⟨[j],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ σ.rightExt t 0 q at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hNOn : N ∈ σ.levelsOn t 0 :=
    List.mem_filter.mpr ⟨hN, by simp [hNt]⟩
  have hpx : p ≠ x := by
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    intro h
    subst x
    simp [hc] at he
  by_cases hxp : x < p
  · left
    refine ⟨hxp, ?_⟩
    have hl := hOneLeft N p x hNOn hx hxp
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    omega
  · right
    have hpx' : p < x := by omega
    refine ⟨hpx', ?_⟩
    have hrank := hOneRight N p x hNOn hx hpx'
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    omega

end ErdosSzekeres
