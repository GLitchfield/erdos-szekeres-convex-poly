import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

/-- A context with two nonempty child runs separated entirely by copies of one level-one external letter has the same bound after shortening both child runs to singletons, provided all older external letters lie outside the two runs. Parameters, sibling maxima, and separator multiplicity stay fixed. This restricted conjecture is a proposed reduction for single-run sandwich additivity; unrestricted child contraction is false.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_single_run
@falsifier ctx_approved_uniform.py -/
theorem ctx_bound_uniform_separator_contraction (σ : Ctx.Context) (hwf : σ.WellFormed)
  (left right : List Ctx.Letter) (r m t : ℕ) (side : Ctx.Side)
  (hr : 0 < r) (hm : 0 < m) (ht : 0 < t)
  (houter : ∀ x ∈ left ++ right, ∃ l s, 2 ≤ l ∧ x = Ctx.Letter.ext l s)
  (hword : σ.word = left ++ List.replicate r Ctx.Letter.child ++
    List.replicate m (Ctx.Letter.ext 1 side) ++ List.replicate t Ctx.Letter.child ++ right) :
  σ.bound = ({ σ with
    word := left ++ [Ctx.Letter.child] ++ List.replicate m (Ctx.Letter.ext 1 side) ++
      [Ctx.Letter.child] ++ right } : Ctx.Context).bound := by
  sorry

end ErdosSzekeres
