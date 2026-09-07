import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Adjacent identical-letter contraction leaves the context bound unchanged, with parameters and sibling maxima fixed. Repeated application to child and external letters would reduce arbitrary three-block sandwiches to the proved singleton-ended case. The substantive child-copy step must absorb recursive cuts that separate the copies; bounded tests require allowing both the coupling and orientation of the dominating contracted cut to change. This statement is a conjecture, not a proved reduction.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_single_run
@falsifier ctx_adjacent_contraction.py -/
theorem ctx_bound_adjacent_letter_contraction (σ : Ctx.Context) (hwf : σ.WellFormed)
  (left right : List Ctx.Letter) (letter : Ctx.Letter)
  (hword : σ.word = left ++ [letter, letter] ++ right) :
  σ.bound = ({ σ with word := left ++ [letter] ++ right } : Ctx.Context).bound := by
  sorry

end ErdosSzekeres
