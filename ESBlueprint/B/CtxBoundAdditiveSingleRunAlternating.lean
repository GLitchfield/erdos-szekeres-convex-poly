import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxBoundChildRunContractionOfLevelOneSpan
import ESBlueprint.B.CtxBoundExtLetterDeletionMonoOfIsolatedChildren
import ESBlueprint.B.CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion

namespace ErdosSzekeres

/-- Alternating single-run additivity (C3; R1, runs/claude-comb-reduction-20260929): for a well-formed single-run context with at least two child letters, the partition keeping every second child position (starting at the first, r = 0, or the second, r = 1) satisfies the additivity inequality in both orientations at every admissible coupling. With run contraction under level-one spans (ctx_bound_child_run_contraction_of_level_one_span, C1) and ctx_bound_external_letter_contraction this gives ctx_bound_additive_single_run through ctx_bound_additive_single_run_of_run_contraction_and_alternating. Run lengths 2 and 3 are covered by the closed prefix/suffix and singleton-ended sandwich nodes. Evidence (compiled evaluator, diagnostic): 0 violations up to run length 10 in ten triples; comb part bounds are constant from run length 6 (runs/claude-comb-reduction-20260929/p6).
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_single_run
@falsifier ctx_bound_additive_single_run_alternating.py -/
theorem ctx_bound_additive_single_run_alternating (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (h2 : 2 ≤ σ.childPositions.length) (r : ℕ) (hr : r < 2) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : let keep := ((List.range σ.childPositions.length).filter (fun i => i % 2 = r)).map (fun i => σ.childPositions.getD i 0); (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  -- C3 from C1 (open) and DelMono (closed) through the closed reduction (R7-R9)
  exact ctx_bound_additive_single_run_alternating_of_run_contraction_and_deletion
    (fun τ hτ side left right hword hspan =>
      ctx_bound_child_run_contraction_of_level_one_span τ hτ side left right hword hspan)
    (fun τ hτ hiso left right lev side hword hother =>
      ctx_bound_ext_letter_deletion_mono_of_isolated_children τ hτ hiso left right lev side hword hother)
    σ hwf hruns h2 r hr d hd hdk

end ErdosSzekeres
