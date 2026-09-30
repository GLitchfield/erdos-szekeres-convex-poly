import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- Run contraction under level-one spans (C1; R1, runs/claude-comb-reduction-20260929): if every letter strictly inside the child span of a well-formed context is a child letter or a level-one external letter of one fixed side, deleting one of two adjacent child letters leaves the bound unchanged. Repeated, every child run shortens to one letter; the two-run case is ctx_bound_uniform_separator_contraction. The unrestricted law is false (ctx_bound_adjacent_letter_contraction_counterexample, a level-two letter inside the span), and so are the adjacent-gap and level-count run-length laws (runs/claude-comb-reduction-20260929/p3, p5). Together with ctx_bound_additive_single_run_alternating (C3) it gives single-run additivity through ctx_bound_additive_single_run_of_run_contraction_and_alternating. Evidence (compiled evaluator, diagnostic): 97,487 contexts over twelve parameter triples with 0 mismatches, and 104,855 for the level-two generalization (runs/claude-comb-reduction-20260929/p1c.json, p1prime-*.json).
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_single_run
@falsifier ctx_level_one_span_run_contraction.py -/
theorem ctx_bound_child_run_contraction_of_level_one_span (σ : Ctx.Context) (hwf : σ.WellFormed) (side : Ctx.Side) (left right : List Ctx.Letter) (hword : σ.word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right) (hspan : ∀ i ∈ σ.childPositions, ∀ j ∈ σ.childPositions, ∀ l : ℕ, i < l → l < j → σ.letterAt l = Ctx.Letter.child ∨ σ.letterAt l = Ctx.Letter.ext 1 side) : σ.bound = ({ σ with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).bound := by
  sorry

end ErdosSzekeres
