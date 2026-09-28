import ESBlueprint.B.CtxNonunitStraddlingUniqueAxisLevel
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- An actual chosen-axis marker straddled by two children whose chosen pure chain extensions are at most one forces every actual indexed chosen-axis marker to use the same level and lie strictly between those children. No global-capacity, k, positivity or activity premise is required. Reuses the earlier nonunit/global-four geometric theorem in an auxiliary context with unchanged word and history, globals four and an enlarged k that makes both witness capacities at least two. Isolates the pure geometry needed for maximal-capacity witnesses in higher-degree rank potentials.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_chain_one_straddling_unique_axis_level (σ : Ctx.Context) (s : Ctx.Side) (N x p q : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions)
  (hpx : p < x) (hxq : x < q)
  (hpchain : σ.chainExt s p p ≤ 1) (hqchain : σ.chainExt s q q ≤ 1) :
  ∀ j ∈ σ.levelsOn s 0, ∀ y ∈ σ.extPositions j, j = N ∧ p < y ∧ y < q := by
  classical
  let K := max (σ.joinExt s p p) (σ.joinExt s q q) + 3
  let τ : Context := { σ with a := 4, u := 4, k := K }
  have hCap (r : ℕ) (hc : σ.chainExt s r r ≤ 1)
      (hj : σ.joinExt s r r ≤ max (σ.joinExt s p p) (σ.joinExt s q q)) :
      2 ≤ (match s with | Side.lower => τ.cupLimit r r | Side.upper => τ.capLimit r r) := by
    cases s
    · change 2 ≤ min (3 - σ.chainExt Side.lower r r)
        ((max (σ.joinExt Side.lower p p) (σ.joinExt Side.lower q q) + 3) - 1 - σ.joinExt Side.lower r r)
      omega
    · change 2 ≤ min (3 - σ.chainExt Side.upper r r)
        ((max (σ.joinExt Side.upper p p) (σ.joinExt Side.upper q q) + 3) - 1 - σ.joinExt Side.upper r r)
      omega
  have hpc := hCap p hpchain (Nat.le_max_left _ _)
  have hqc := hCap q hqchain (Nat.le_max_right _ _)
  have hg : (match s with | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
    cases s <;> exact le_rfl
  exact ctx_nonunit_straddling_unique_axis_level τ s N x p q hN hNs hx hp hq hpc hqc hpx hxq hg

end ErdosSzekeres
