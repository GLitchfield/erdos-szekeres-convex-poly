import ESBlueprint.B.CtxBoundLeMergeSameSideLevels
import ESBlueprint.B.CtxBoundZeroOfUnitGlobalAxis
import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxBoundCutLe
import ESBlueprint.B.CtxTwoBoundaryMarkerUpperNormalize
import ESBlueprint.B.CtxPartBoundZeroOfSameSideLargeSiblingMaximum
import ESBlueprint.B.CtxBoundReverse
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum
import ESBlueprint.B.CtxSingleLevelLimitsExact
import ESBlueprint.B.CtxSingletonPartBoundEqThreshold
import ESBlueprint.B.CtxPartPositiveLetters
import ESBlueprint.B.CtxPositiveBoundAttainedByIntervalCut
import ESBlueprint.B.CtxBoundaryMarkerUpperNormalize
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential
import ESBlueprint.B.CtxUnitAxisActiveRegionPotential
import ESBlueprint.B.CtxChainOneChildrenExteriorOfTwoLevels

set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

namespace ErdosSzekeres
open Ctx Ctx.Context MergeLevels

/-- Kernel-certified obstruction to a contraction-stable class containing every proper legal one-level-root cut complement: a well-formed uniform5/5/k6/max1 root with two runs and proper block[1], coupled maxima4/1, has the exact lower complement word[child,ext1lower,ext2upper,child,child]/maxima[1,1]. Its adjacent child sites3/4 have full bound12, while contraction gives9. Ordinary kernel decide certifies both values. This is not a C1r or ROOT-NF refutation; whole-cut reoptimization remains open.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_one_level_root_cut_complement_child_contraction_counterexample :
    let σ : Ctx.Context := ⟨5, 5, 6, [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child], [1]⟩
    let block : List ℕ := [1]
    let rest := σ.childPositions.filter (fun p => p ∉ block)
    let ρ := σ.part rest Ctx.Side.lower (σ.k - 1 - 4)
    let τ : Ctx.Context := {ρ with word := ρ.word.take 4 ++ ρ.word.drop 5}
    σ.WellFormed ∧
      (∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 Ctx.Side.upper) ∧
      σ.numRuns = 2 ∧ block ∈ σ.blocks ∧
      1 ≤ 4 ∧ 4 ≤ σ.k - 2 ∧
      1 ≤ σ.k - 1 - 4 ∧ σ.k - 1 - 4 ≤ σ.k - 2 ∧
      ρ.word = [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
        Ctx.Letter.ext 2 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child] ∧
      ρ.maxima = [1, 1] ∧
      ρ.letterAt 3 = Ctx.Letter.child ∧ ρ.letterAt 4 = Ctx.Letter.child ∧
      ρ.bound = 12 ∧ τ.bound = 9 ∧ ρ.bound ≠ τ.bound := by
  let σ : Ctx.Context := ⟨5, 5, 6, [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child], [1]⟩
  let block : List ℕ := [1]
  let rest := σ.childPositions.filter (fun p => p ∉ block)
  let ρ := σ.part rest Ctx.Side.lower (σ.k - 1 - 4)
  let τ : Ctx.Context := {ρ with word := ρ.word.take 4 ++ ρ.word.drop 5}
  change σ.WellFormed ∧
    (∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 Ctx.Side.upper) ∧
    σ.numRuns = 2 ∧ block ∈ σ.blocks ∧
    1 ≤ 4 ∧ 4 ≤ σ.k - 2 ∧
    1 ≤ σ.k - 1 - 4 ∧ σ.k - 1 - 4 ≤ σ.k - 2 ∧
    ρ.word = [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
      Ctx.Letter.ext 2 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child] ∧
    ρ.maxima = [1, 1] ∧
    ρ.letterAt 3 = Ctx.Letter.child ∧ ρ.letterAt 4 = Ctx.Letter.child ∧
    ρ.bound = 12 ∧ τ.bound = 9 ∧ ρ.bound ≠ τ.bound
  have hwf : σ.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [σ]
    · intro p l s hletter
      have hp : p < 5 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le _ (show 5 ≤ p by omega)] at hletter
        cases hletter
      interval_cases p <;> simp [σ, Ctx.Context.letterAt] at hletter
      all_goals
        rcases hletter with ⟨rfl, rfl⟩
        decide
  have hlarge : ρ.bound = 12 := by
    set_option maxRecDepth 10000 in decide
  have hsmall : τ.bound = 9 := by
    set_option maxRecDepth 10000 in decide
  refine ⟨hwf, ?_, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    hlarge, hsmall, ?_⟩
  · simp [σ]
  · rw [hlarge, hsmall]
    decide

end ErdosSzekeres
