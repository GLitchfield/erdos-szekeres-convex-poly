import ErdosSzekeres.DecomposableContextLemmas
import ESBlueprint.B.CtxBoundChildRunContractionOneLevelRoot
import ESBlueprint.B.CtxBoundPartRunContractionOfOneLevelRoot
import ESBlueprint.B.CtxBoundAdditiveSingleRunAlternating
import ESBlueprint.B.CtxBoundAdditiveSingleRunOfPartContractionAndAlternating

namespace ErdosSzekeres

/-- Additivity of the context bound for a single-run context: the bound is the classical threshold with the run internal limits, and every partition of the run (any interleaving), both orientations and every coupling d, gives part bounds summing to at most it. This is the Baek-Balko one-level inequality with the full positional context (experiments 0118, 0120-0122); the falsifier is the general additivity test, which covers this case.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive
@falsifier ctx_bound_additive.py -/
theorem ctx_bound_additive_single_run (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  -- R6' applied to part contraction (the bridge applied to C1r) and C3 (itself from C1r):
  -- single-run additivity depends only on ctx_bound_child_run_contraction_one_level_root
  exact ctx_bound_additive_single_run_of_part_contraction_and_alternating
    (fun τ hτ hruns keep s m hm hmk left right hword =>
      ctx_bound_part_run_contraction_of_one_level_root
        (fun a u k m hk ha hak hu huk hm hmk side left right hletters =>
          ctx_bound_child_run_contraction_one_level_root a u k m hk ha hak hu huk hm hmk side left right hletters)
        τ hτ hruns keep s m hm hmk left right hword)
    (fun τ hτ hruns h2 r hr d hd hdk => ctx_bound_additive_single_run_alternating τ hτ hruns h2 r hr d hd hdk)
    σ hwf hruns keep hkeep hne hall d hd hdk

end ErdosSzekeres
