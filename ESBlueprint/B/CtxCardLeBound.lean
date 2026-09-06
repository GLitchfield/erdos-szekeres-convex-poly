import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- The context induction (experiments 0117-0121): a decomposable coloring on S that satisfies the constraints of a well-formed context σ has at most bound σ vertices. Induction on IsDecomposableOn: split, transfer the context to both parts (ctx_satisfies_of_deepBelowSplit), apply the hypothesis, dominate the two-parameter coupling by the one-parameter one (ctx_bound_antitone), and finish with the additivity conjecture (ctx_bound_additive). At the root context this is DecomposableStateUpper for all parameters.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_satisfies_of_deepBelowSplit, ErdosSzekeres.ctx_bound_antitone, ErdosSzekeres.ctx_bound_additive
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem ctx_card_le_bound {n : ℕ} {χ : TripleColoring n} {S : Finset (Fin n)} (σ : Ctx.Context) (hwf : σ.WellFormed) (hdec : IsDecomposableOn χ S) (hS : Ctx.Satisfies χ S σ) : S.card ≤ σ.bound := by
  sorry

end ErdosSzekeres
