import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxOneLevelRootBoundAttainedBySingletonCut
import ESBlueprint.B.CtxOneLevelRootSingletonBaseExchange
import ESBlueprint.B.CtxBoundChildRunContractionOneLevelRootOfSingletonExchange

namespace ErdosSzekeres

/-- Run contraction for one external level over a bare root (C1r): in a context with parameters 1 <= a, u <= k, one level of maximum m in [1, k-2] and a word of child letters and level-one letters of one side, deleting one of two adjacent child letters leaves the bound unchanged. This is the normalized form of C1 as the single-run chain uses it: every part of a single-run context has the bound of such a context with (a, u) = (capLimit + 1, cupLimit + 1) of the run (ctx_single_run_descendant_bound_normalize), so C1 for parts of single-run contexts follows from this node (bridge node), and single-run additivity then depends only on it (R7, runs/claude-comb-closedform-20260930). Evidence (compiled evaluator, diagnostic): no C1 violation, and every separating cut dominated by a moved partition after re-optimizing the coupling, over all a, u, m, sides and ends with <= 5 children at k = 5, 6, 7 (runs/claude-comb-closedform-20260930/c1r).
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_single_run
@falsifier ctx_one_level_root_run_contraction.py -/
theorem ctx_bound_child_run_contraction_one_level_root (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2) (side : Ctx.Side) (left right : List Ctx.Letter) (hletters : ∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) : ({ a := a, u := u, k := k, word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, maxima := [m] } : Ctx.Context).bound = ({ a := a, u := u, k := k, word := left ++ [Ctx.Letter.child] ++ right, maxima := [m] } : Ctx.Context).bound := by
  classical
  have hrootLetters : ∀ x ∈ left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right,
      x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side := by
    intro x hx
    by_cases hc : x = Ctx.Letter.child
    · exact Or.inl hc
    · apply hletters x
      simpa [hc, List.mem_append] using hx
  exact ctx_bound_child_run_contraction_one_level_root_of_singleton_exchange
    a u k m hk ha hak hu huk hm hmk side left right hletters
    (ctx_one_level_root_bound_attained_by_singleton_cut a u k m hk ha hak hu huk hm hmk
      side (left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right) hrootLetters)
    (ctx_one_level_root_singleton_base_exchange a u k m hk ha hak hu huk hm hmk
      side left right hletters)

end ErdosSzekeres
