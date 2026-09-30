import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every singleton child part has the explicit decomposable threshold value of its point cap and cup limits. Covers arbitrary raw contexts and sibling maxima, including zero and unit capacities, without a well-formedness assumption. Supplies the exact single-child T term for the one-level-root contraction exchange.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_singleton_part_bound_eq_threshold (σ : Ctx.Context) (p : ℕ) (hp : p ∈ σ.childPositions) (s : Ctx.Side) (m : ℕ) : (σ.part [p] s m).bound = decomposableThreshold ((σ.part [p] s m).capLimit p p + 1) ((σ.part [p] s m).cupLimit p p + 1) σ.k := by
  have hBase : ∀ cl pl k : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
      baseOf cl pl k = decomposableThreshold (pl + 1) (cl + 1) k := by
    intro cl pl k hc hpl
    by_cases hz : cl = 0 ∨ pl = 0
    · rcases hz with rfl | rfl <;> simp [baseOf]
    unfold baseOf
    rw [if_neg hz]
    by_cases hunit : cl = 1 ∨ pl = 1
    · rw [if_pos hunit]
      rcases hunit with rfl | rfl
      · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
        have hrow : pl + 1 + (1 + 1) - 4 = pl + 1 - 2 := by omega
        rw [hrow, Nat.choose_self]
      · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
        simp
    · rw [if_neg hunit]
  have hfilter : σ.childPositions.filter (· ∈ [p]) = [p] := by
    let L := σ.childPositions.filter (· ∈ [p])
    change L = [p]
    have hn : L.Nodup := (childPositions_nodup σ).filter _
    have hsub : L ⊆ [p] := fun q hq ↦ of_decide_eq_true (List.mem_filter.mp hq).2
    have hle : L.length ≤ 1 := by
      simpa using (hn.subperm hsub).length_le
    have hmem : p ∈ L := by simp [L, hp]
    cases hL : L with
    | nil => simp [hL] at hmem
    | cons q qs =>
      have hq : q = p := by
        have h := hsub (by simp [hL] : q ∈ L)
        simpa using h
      have hqs : qs = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [hL, List.length_cons] at hle
        omega
      simpa only [hL, hq, hqs]
  have hps : (σ.part [p] s m).childPositions = [p] := by
    rw [part_childPositions]
    exact hfilter
  have hruns : (σ.part [p] s m).numRuns ≤ 1 := by
    simpa only [hps, List.length_singleton] using numRuns_le_length (σ.part [p] s m)
  rw [Context.bound, boundFuel.eq_2, if_pos hruns, base_eq_baseOf, hps]
  change baseOf ((σ.part [p] s m).cupLimit p p) ((σ.part [p] s m).capLimit p p) σ.k = _
  apply hBase
  · simp only [cupLimit, part_k]
    omega
  · simp only [capLimit, part_k]
    omega

end ErdosSzekeres
