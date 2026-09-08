import ESBlueprint.B.CtxBoundAdditiveDisjointSingleRunSmallAxis

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Conditional additivity for a contiguous middle interval and its two outer blocks in a single ancestor child run. If the ancestor cup capacity is at most two, lower outer plus upper middle is bounded by the parent; if its cap capacity is at most two, the dual orientation is bounded. The three blocks may have arbitrary positive lengths and both new maxima are arbitrary natural numbers. The two capacity assumptions govern separate orientations. Applies arbitrary-disjoint single-run small-capacity additivity; this special case removes the unbounded outer-length obstruction in the corresponding orientations.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_interval_complement_small_outer_axis (σ : Ctx.Context) (hwf : σ.WellFormed)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r) (outerMax middleMax : ℕ) :
  (σ.cupLimit b b ≤ 2 →
    (σ.part (List.range' b l ++ List.range' (b + l + m) r)
      Ctx.Side.lower outerMax).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.upper middleMax).bound ≤ σ.bound) ∧
  (σ.capLimit b b ≤ 2 →
    (σ.part (List.range' b l ++ List.range' (b + l + m) r)
      Ctx.Side.upper outerMax).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.lower middleMax).bound ≤ σ.bound) := by
  classical
  have hpositive : ∀ x j v, σ.letterAt x = Letter.ext j v → 1 ≤ j :=
    fun x j v hx => (hwf.2.2.2.2.2 x j v hx).1
  have hdis : ∀ p ∈ σ.childPositions,
      p ∈ List.range' b l ++ List.range' (b + l + m) r → p ∉ List.range' (b + l) m := by
    intro p _ hp hm'
    have hmpos := List.mem_range'_1.mp hm'
    rcases List.mem_append.mp hp with hl' | hr'
    · have hlpos := List.mem_range'_1.mp hl'
      omega
    · have hrpos := List.mem_range'_1.mp hr'
      omega
  constructor
  · intro hc
    exact ctx_bound_additive_disjoint_single_run_small_axis σ hpositive b (l + m + r) hpos
      (by omega) ((Nat.min_le_left _ _).trans hc) _ _ Side.lower Side.upper (by decide)
      outerMax middleMax hdis
  · intro hp
    exact ctx_bound_additive_disjoint_single_run_small_axis σ hpositive b (l + m + r) hpos
      (by omega) ((Nat.min_le_right _ _).trans hp) _ _ Side.upper Side.lower (by decide)
      outerMax middleMax hdis

end ErdosSzekeres
