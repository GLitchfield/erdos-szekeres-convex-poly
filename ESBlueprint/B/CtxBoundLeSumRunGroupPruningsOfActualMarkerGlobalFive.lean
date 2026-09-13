import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every-fuel and full run-group pruning decomposition from one actual chosen marker at global at most five. The actual marker forces at least one pure chosen extension at every child, hence every child has minimum point capacity at most three; the checked capacity-three decomposition then applies to arbitrary finite run-constant colorings. Positive labels, arbitrary maxima and histories, inactive children, empty groups and either axis are retained. This exports a bridge used only locally in prior rank-potential proofs and prepares the residual six-extreme companion for groupwise accounting. Exact search in runs/sol-12h/search-actual-marker-global-five-run-group-pruning.json found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_sum_run_group_prunings_capacity_three
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (color : ℕ → ℕ) (colors : Finset ℕ) (hcover : ∀ p ∈ σ.childPositions, color p ∈ colors) (hcolor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, p ≤ q → (∀ r, p ≤ r → r ≤ q → r ∈ σ.childPositions) → color p = color q) : let support := fun c => σ.childPositions.filter (fun p => color p = c); let group := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ colors.sum (fun c => (group c).bound)) ∧ σ.bound ≤ colors.sum (fun c => (group c).bound) := by
  classical
  have hNOn : N ∈ σ.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hOneLeft (p : ℕ) (hxp : x < p) : 1 ≤ σ.leftExt s 0 p := by
    have hm : x ∈ (σ.extPositions N).filter (· < p) := by
      simp [hx, hxp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (leftStep σ) (p, 0)).2))
      (List.mem_map.mpr
        ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
    change _ ≤ σ.leftExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (p : ℕ) (hpx : p < x) : 1 ≤ σ.rightExt s 0 p := by
    have hm : x ∈ (σ.extPositions N).filter (p < ·) := by
      simp [hx, hpx]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (rightStep σ) (p, 0)).2))
      (List.mem_map.mpr
        ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
    change _ ≤ σ.rightExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hChain (p : ℕ) (hp : p ∈ σ.childPositions) :
      1 ≤ σ.chainExt s p p := by
    have hletter : σ.letterAt p = Letter.child :=
      of_decide_eq_true (List.mem_filter.mp hp).2
    have hpx : p ≠ x := by
      intro heq
      subst p
      simp [extPositions, hletter] at hx
    rcases lt_or_gt_of_ne hpx with hpx | hxp
    · have hr := hOneRight p hpx
      simp only [chainExt]
      omega
    · have hl := hOneLeft p hxp
      simp only [chainExt]
      omega
  have hsmall : ∀ p ∈ σ.childPositions,
      min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
    intro p hp
    have hc := hChain p hp
    cases s with
    | lower =>
        have hg : σ.u ≤ 5 := by simpa using hglobal
        calc
          min (σ.cupLimit p p) (σ.capLimit p p) ≤ σ.cupLimit p p :=
            Nat.min_le_left _ _
          _ ≤ σ.u - 1 - σ.chainExt Side.lower p p := by
            simp only [cupLimit]
            exact Nat.min_le_left _ _
          _ ≤ 3 := by omega
    | upper =>
        have hg : σ.a ≤ 5 := by simpa using hglobal
        calc
          min (σ.cupLimit p p) (σ.capLimit p p) ≤ σ.capLimit p p :=
            Nat.min_le_right _ _
          _ ≤ σ.a - 1 - σ.chainExt Side.upper p p := by
            simp only [capLimit]
            exact Nat.min_le_left _ _
          _ ≤ 3 := by omega
  exact ctx_bound_le_sum_run_group_prunings_capacity_three σ hpositive color colors
    hcover hsmall hcolor


end ErdosSzekeres
