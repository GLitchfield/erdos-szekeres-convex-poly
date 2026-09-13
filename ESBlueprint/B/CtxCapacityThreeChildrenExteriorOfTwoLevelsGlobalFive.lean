import ESBlueprint.B.CtxChainOneChildrenExteriorOfTwoLevels

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At global parameter at most five, two distinct actual indexed levels on one chosen axis force every child with chosen-axis capacity at least three into one common exterior marker region. Capacity at least three implies pure chosen chain extension at most one, so the existing chain-one exterior theorem supplies the orientation. This isolates the only maximal-capacity group in the residual six-extreme sandwich case. Exact search in runs/sol-12h/search-capacity-three-common-exterior-global-five.json found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_chain_one_children_exterior_of_two_levels
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_capacity_three_children_exterior_of_two_levels_global_five (σ : Ctx.Context) (s : Ctx.Side) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) : (x < y ∧ ∀ p ∈ σ.childPositions, 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p) → ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z < p) ∨ (y < x ∧ ∀ p ∈ σ.childPositions, 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p) → ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, p < z) := by
  have hChain (p : ℕ)
      (hcap : 3 ≤ (match s with
        | Side.lower => σ.cupLimit p p
        | Side.upper => σ.capLimit p p)) :
      σ.chainExt s p p ≤ 1 := by
    cases hs : s <;> simp only [hs] at hglobal hcap ⊢
    · simp only [cupLimit] at hcap
      omega
    · simp only [capLimit] at hcap
      omega
  rcases ctx_chain_one_children_exterior_of_two_levels σ s N M x y
      hN hM hNM hNs hMs hx hy with hl | hr
  · exact Or.inl ⟨hl.1, fun p hp hcap => hl.2 p hp (hChain p hcap)⟩
  · exact Or.inr ⟨hr.1, fun p hp hcap => hr.2 p hp (hChain p hcap)⟩


end ErdosSzekeres
