import ESBlueprint.B.CtxPointLimitsEqOfChildInterval
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsOfActualMarkerGlobalFive

namespace ErdosSzekeres

/-- Every-fuel and full context bound decompose canonically into the four original-history prunings selected by chosen-axis point capacities zero through three, in the presence of one actual marker and chosen global at most five. The marker caps every chosen capacity at three, while point limits are constant across uninterrupted child intervals, so capacity is a valid physical-run coloring for the checked run-group decomposition. This names the capacity-three pruning whose common exterior geometry must supply the residual strict saving. Exact search in runs/sol-12h/search-capacity-pruning-decomposition.json found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five, ErdosSzekeres.ctx_point_limits_eq_of_child_interval
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_le_sum_chosen_capacity_prunings_of_actual_marker_global_five (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) : let capacity := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let support := fun c => σ.childPositions.filter (fun p => capacity p = c); let group := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (Finset.range 4).sum (fun c => (group c).bound)) ∧ σ.bound ≤ (Finset.range 4).sum (fun c => (group c).bound) := by
  classical
  let C (v : Ctx.Side) (p : ℕ) := match v with
    | Ctx.Side.lower => σ.cupLimit p p
    | Ctx.Side.upper => σ.capLimit p p
  open Ctx Ctx.Context in
    have hNOn : N ∈ σ.levelsOn s 0 :=
      List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
    have hOneLeft (p : ℕ) (hxp : x < p) : 1 ≤ σ.leftExt s 0 p := by
      have hm : x ∈ (σ.extPositions N).filter (· < p) := by simp [hx, hxp]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (leftStep σ) (p, 0)).2))
        (List.mem_map.mpr
          ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
      change _ ≤ σ.leftExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, leftStep,
        List.getLast?_eq_some_getLast hnonempty] using hv
    have hOneRight (p : ℕ) (hpx : p < x) : 1 ≤ σ.rightExt s 0 p := by
      have hm : x ∈ (σ.extPositions N).filter (p < ·) := by simp [hx, hpx]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (rightStep σ) (p, 0)).2))
        (List.mem_map.mpr
          ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
      change _ ≤ σ.rightExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, rightStep,
        List.head?_eq_some_head hnonempty] using hv
    have hChain (p : ℕ) (hp : p ∈ σ.childPositions) : 1 ≤ σ.chainExt s p p := by
      have hletter : σ.letterAt p = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hp).2
      have hpx : p ≠ x := by
        intro heq
        subst p
        simp [Ctx.Context.extPositions, hletter] at hx
      rcases lt_or_gt_of_ne hpx with hpx | hxp
      · have hr := hOneRight p hpx
        simp only [Ctx.Context.chainExt]
        omega
      · have hl := hOneLeft p hxp
        simp only [Ctx.Context.chainExt]
        omega
    have hcover : ∀ p ∈ σ.childPositions,
        C s p ∈ Finset.range 4 := by
      intro p hp
      simp only [Finset.mem_range]
      have hc := hChain p hp
      by_cases hs : s = Ctx.Side.lower
      · have hg : σ.u ≤ 5 := by simpa only [hs] using hglobal
        have hc' : 1 ≤ σ.chainExt Ctx.Side.lower p p := by simpa only [hs] using hc
        simp only [C, hs]
        calc
          σ.cupLimit p p ≤ σ.u - 1 - σ.chainExt Ctx.Side.lower p p := by
            simp only [Ctx.Context.cupLimit]
            exact Nat.min_le_left _ _
          _ < 4 := by omega
      · have hsu : s = Ctx.Side.upper := by
          cases s <;> simp_all
        have hg : σ.a ≤ 5 := by simpa only [hsu] using hglobal
        have hc' : 1 ≤ σ.chainExt Ctx.Side.upper p p := by simpa only [hsu] using hc
        simp only [C, hsu]
        calc
          σ.capLimit p p ≤ σ.a - 1 - σ.chainExt Ctx.Side.upper p p := by
            simp only [Ctx.Context.capLimit]
            exact Nat.min_le_left _ _
          _ < 4 := by omega
    have hcolor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, p ≤ q →
        (∀ r, p ≤ r → r ≤ q → r ∈ σ.childPositions) →
        C s p = C s q := by
      intro p hp q hq hpq hinterval
      have hh := ctx_point_limits_eq_of_child_interval σ p q hp hq hpq hinterval
      by_cases hs : s = Ctx.Side.lower
      · simpa only [C, hs] using hh.1
      · have hsu : s = Ctx.Side.upper := by
          cases s <;> simp_all
        simpa only [C, hsu] using hh.2
    simpa only [C] using
      (ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five
      σ hpositive s N x hN hNs hx hglobal
      (C s) (Finset.range 4) hcover hcolor)


end ErdosSzekeres
