import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- Bridge from the root form of run contraction (C1r, hypothesis hroot) to run contraction in every part of a well-formed single-run context (C1p): by ctx_single_run_descendant_bound_normalize the part and its contraction have the bounds of the normalized one-level contexts with (a, u) = (capLimit + 1, cupLimit + 1) of the run (the same for both, since all children of a single run have equal point limits); the older letters are inert there and lie outside the child span, so deleting them leaves the bound unchanged, which gives a word over child and level-one letters of one side, where hroot applies. No proof of hroot is asserted (R7/R10, runs/claude-comb-closedform-20260930).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_single_run_descendant_bound_normalize
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_part_run_contraction_of_one_level_root (hroot : ∀ (a u k m : ℕ), 3 ≤ k → 1 ≤ a → a ≤ k → 1 ≤ u → u ≤ k → 1 ≤ m → m ≤ k - 2 → ∀ (side : Ctx.Side) (left right : List Ctx.Letter), (∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) → ({ a := a, u := u, k := k, word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, maxima := [m] } : Ctx.Context).bound = ({ a := a, u := u, k := k, word := left ++ [Ctx.Letter.child] ++ right, maxima := [m] } : Ctx.Context).bound) (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (keep : List ℕ) (s : Ctx.Side) (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ σ.k - 2) (left right : List Ctx.Letter) (hword : (σ.part keep s m).word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right) : (σ.part keep s m).bound = ({ σ.part keep s m with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).bound := by
  sorry

end ErdosSzekeres
