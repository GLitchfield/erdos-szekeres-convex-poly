import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Coloring-context constraint transport with equal child-position lists, nondecreasing k and nondecreasing cup/cap limits at child endpoints. Every Satisfies coloring remains satisfied; no WellFormed or global parameter premise is needed. Ambient subset min/max endpoints have child positions by the existing rank-membership helper. Supplies the coloring-constraint side of R19 exact normalization verification, without claiming complete actual history realization.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.Ctx.Context.pos_mem_childPositions
@consumer ErdosSzekeres.ctx_card_le_bound -/
theorem ctx_satisfies_of_limits_le {n : ℕ} (χ : TripleColoring n) (S : Finset (Fin n)) (σ τ : Ctx.Context)
(hpositions : σ.childPositions = τ.childPositions) (hk : σ.k ≤ τ.k)
(hlimits : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
  σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q)
(hs : Ctx.Satisfies χ S σ) : Ctx.Satisfies χ S τ := by
  classical
  refine ⟨?_, ?_⟩
  · rw [← hpositions]
    exact hs.1
  · intro C hCS hC
    dsimp only
    rw [← hpositions]
    have hp := Ctx.Context.pos_mem_childPositions hs.1 (hCS (Finset.min'_mem C hC))
    have hq := Ctx.Context.pos_mem_childPositions hs.1 (hCS (Finset.max'_mem C hC))
    have hl := hlimits _ hp _ hq
    have h := hs.2 C hCS hC
    exact ⟨fun hc => (h.1 hc).trans hl.1,
      fun hc => (h.2.1 hc).trans hl.2,
      fun hc => (h.2.2 hc).trans (Nat.sub_le_sub_right hk 1)⟩

end ErdosSzekeres
