import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Coloring constraints transport under equal ordinal child counts and nondecreasing cup/cap limits at corresponding ordinal endpoints, with nondecreasing k and no WellFormed assumptions. Ambient min/max ranks identify the corresponding children, supplying the renumbering invariant needed after literal exterior-padding erasure.
@node
@ws B
@kind formalization
@dangling-ok Removes R19 Satisfies renumbering obstruction after accepted exterior-padding bound transport; reusable ordinal constraint invariant. -/
theorem ctx_satisfies_of_ordinal_limits_le {n : ℕ} (χ : TripleColoring n) (S : Finset (Fin n)) (σ τ : Ctx.Context)
  (hlen : σ.childPositions.length = τ.childPositions.length)
  (hk : σ.k ≤ τ.k)
  (hlimits : ∀ i j : ℕ, i < σ.childPositions.length → j < σ.childPositions.length →
    σ.cupLimit ((σ.childPositions[i]?).getD 0) ((σ.childPositions[j]?).getD 0) ≤
      τ.cupLimit ((τ.childPositions[i]?).getD 0) ((τ.childPositions[j]?).getD 0) ∧
    σ.capLimit ((σ.childPositions[i]?).getD 0) ((σ.childPositions[j]?).getD 0) ≤
      τ.capLimit ((τ.childPositions[i]?).getD 0) ((τ.childPositions[j]?).getD 0))
  (hs : Ctx.Satisfies χ S σ) : Ctx.Satisfies χ S τ := by
  classical
  refine ⟨hlen.symm.trans hs.1, ?_⟩
  intro C hCS hC
  dsimp only
  have hp : (S.filter (· < C.min' hC)).card < σ.childPositions.length := by
    rw [hs.1]
    exact Ctx.Context.rank_lt_card (hCS (Finset.min'_mem C hC))
  have hq : (S.filter (· < C.max' hC)).card < σ.childPositions.length := by
    rw [hs.1]
    exact Ctx.Context.rank_lt_card (hCS (Finset.max'_mem C hC))
  have hl := hlimits _ _ hp hq
  have h := hs.2 C hCS hC
  exact ⟨fun hc => (h.1 hc).trans hl.1,
    fun hc => (h.2.1 hc).trans hl.2,
    fun hc => (h.2.2 hc).trans (Nat.sub_le_sub_right hk 1)⟩

end ErdosSzekeres
