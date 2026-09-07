import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

/-- Deleting one of two adjacent identical external letters preserves the context bound, with parameters and sibling maxima fixed. The proof must transport child positions, ordered extension folds, and recursive cuts; this makes no assertion about contracting child letters.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_single_run
@falsifier ctx_approved_external.py -/
theorem ctx_bound_external_letter_contraction (σ : Ctx.Context) (hwf : σ.WellFormed)
  (left right : List Ctx.Letter) (lev : ℕ) (side : Ctx.Side)
  (hword : σ.word = left ++ [Ctx.Letter.ext lev side, Ctx.Letter.ext lev side] ++ right) :
  σ.bound = ({ σ with word := left ++ [Ctx.Letter.ext lev side] ++ right } : Ctx.Context).bound := by
  sorry

end ErdosSzekeres
