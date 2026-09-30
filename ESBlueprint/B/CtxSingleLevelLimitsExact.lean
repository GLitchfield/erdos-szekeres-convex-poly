import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact endpoint extension and capacity formulas for any raw context with one indexed sibling level and global parameters at most k. On the level's selected side, joinExt is max(chainExt,m), so the chosen limit is min(global-1-chainExt,k-1-m); opposite chain/join vanish and its limit is otherglobal-1. No child membership, well-formedness, physical uniformity or sibling-maximum-range hypotheses. Supplies explicit root capacities for singleton base exchange and capacity-ordered normal-form research.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_single_level_limits_exact (σ : Ctx.Context) (m : ℕ) (hm : σ.maxima = [m])
    (ha : σ.a ≤ σ.k) (hu : σ.u ≤ σ.k) (s : Ctx.Side) (hs : σ.sideAt 1 = s)
    (p q : ℕ) :
    σ.joinExt s p q = max (σ.chainExt s p q) m ∧
    (match s with
    | Ctx.Side.lower =>
        σ.chainExt Ctx.Side.upper p q = 0 ∧ σ.joinExt Ctx.Side.upper p q = 0 ∧
        σ.cupLimit p q = min (σ.u - 1 - σ.chainExt Ctx.Side.lower p q) (σ.k - 1 - m) ∧
        σ.capLimit p q = σ.a - 1
    | Ctx.Side.upper =>
        σ.chainExt Ctx.Side.lower p q = 0 ∧ σ.joinExt Ctx.Side.lower p q = 0 ∧
        σ.capLimit p q = min (σ.a - 1 - σ.chainExt Ctx.Side.upper p q) (σ.k - 1 - m) ∧
        σ.cupLimit p q = σ.u - 1) := by
  have hon : σ.levelsOn s 0 = [1] := by
    simp [levelsOn, levels, hm, hs]
  have hmax : σ.maximumAt 1 = m := by simp [maximumAt, hm]
  have hjoin : σ.joinExt s p q = max (σ.chainExt s p q) m := by
    simp [joinExt, hon, leftExt_one, rightExt_one, hmax]
  refine ⟨hjoin, ?_⟩
  cases s with
  | lower =>
    have hoff : σ.levelsOn Side.upper 0 = [] := by
      simp [levelsOn, levels, hm, hs]
    have hchain : σ.chainExt Side.upper p q = 0 := by
      simp [chainExt, leftExt, rightExt, hoff]
    have hj : σ.joinExt Side.upper p q = 0 := by
      simp [joinExt, hchain, hoff]
    refine ⟨hchain, hj, ?_, ?_⟩
    · unfold cupLimit
      rw [hjoin]
      omega
    · unfold capLimit
      rw [hchain, hj]
      omega
  | upper =>
    have hoff : σ.levelsOn Side.lower 0 = [] := by
      simp [levelsOn, levels, hm, hs]
    have hchain : σ.chainExt Side.lower p q = 0 := by
      simp [chainExt, leftExt, rightExt, hoff]
    have hj : σ.joinExt Side.lower p q = 0 := by
      simp [joinExt, hchain, hoff]
    refine ⟨hchain, hj, ?_, ?_⟩
    · unfold capLimit
      rw [hjoin]
      omega
    · unfold cupLimit
      rw [hchain, hj]
      omega


end ErdosSzekeres
