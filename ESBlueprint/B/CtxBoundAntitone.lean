import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Monotonicity of the context bound in a sibling maximum: raising the longest chain of the sibling at any level does not increase the bound (every limit entering the recursion is antitone in the maxima). Tested on 9,444 comparisons (experiment 0121).
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_card_le_bound -/
theorem ctx_bound_antitone (σ : Ctx.Context) (l m : ℕ) : (σ.withMaximum l (m + 1)).bound ≤ (σ.withMaximum l m).bound := by
  exact Ctx.Context.boundFuel_le _ (Ctx.Context.withMaximum_dominates σ l m)

end ErdosSzekeres
