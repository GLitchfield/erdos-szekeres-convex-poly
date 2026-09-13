import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

/-- A well-formed positive-maxima context with three actual chosen markers in nonmonotone order has bound at least eleven, exceeding the proposed top saturation value ten. The chosen global is five, opposite global and k are six, opposite indexed history is empty, and every chosen maximum is one, strictly below k-4. Thus the large-maximum premise cannot simply be dropped from the nonmonotone-triple saturated potential, even for well-formed histories. This certifies a finite-probe witness and rules out that stronger auxiliary potential; it does not refute context additivity or the Erdős–Szekeres conjecture. Probe: runs/sol-trial-20260913/maximum-positive-probe.json; search: runs/sol-trial-20260913/search-maximum-counterexample.json.
@node
@ws B
@kind refutation
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonmonotone_triple_small_maxima_counterexample : let σ : Ctx.Context := ⟨6, 5, 6,
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
      Ctx.Letter.child, Ctx.Letter.ext 3 Ctx.Side.lower,
      Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  σ.WellFormed ∧ σ.levels = [1, 2, 3] ∧ σ.levelsOn Ctx.Side.upper 0 = [] ∧
    σ.extPositions 1 = [2] ∧ σ.extPositions 2 = [5] ∧ σ.extPositions 3 = [4] ∧
    (∀ j ∈ σ.levels, σ.sideAt j = Ctx.Side.lower ∧ σ.maximumAt j < σ.k - 4) ∧
    11 ≤ σ.bound ∧ 3 * σ.k - 8 = 10 := by
  dsimp only
  let σ : Ctx.Context := ⟨6, 5, 6,
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
      Ctx.Letter.child, Ctx.Letter.ext 3 Ctx.Side.lower,
      Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  change σ.WellFormed ∧ σ.levels = [1, 2, 3] ∧
    σ.levelsOn Ctx.Side.upper 0 = [] ∧
    σ.extPositions 1 = [2] ∧ σ.extPositions 2 = [5] ∧ σ.extPositions 3 = [4] ∧
    (∀ j ∈ σ.levels,
      σ.sideAt j = Ctx.Side.lower ∧ σ.maximumAt j < σ.k - 4) ∧
    11 ≤ σ.bound ∧ 3 * σ.k - 8 = 10

  let C := σ.part [3] Ctx.Side.lower 3
  let D := σ.part [0, 1, 6] Ctx.Side.upper 2
  let E := D.part [0] Ctx.Side.upper 3
  let F := D.part [1, 6] Ctx.Side.lower 2
  let G := F.part [1] Ctx.Side.upper 4
  let H := F.part [6] Ctx.Side.lower 1

  have hσrest : σ.childPositions.filter (fun p ↦ p ∉ [3]) = [0, 1, 6] := by
    decide +kernel
  have hDrest : D.childPositions.filter (fun p ↦ p ∉ [0]) = [1, 6] := by
    decide +kernel
  have hFrest : F.childPositions.filter (fun p ↦ p ∉ [1]) = [6] := by
    decide +kernel

  have hrootRaw := (ctx_bound_cut_le σ (by decide +kernel) [3]
    (by decide +kernel) 3 (by decide) (by decide +kernel)).1
  rw [hσrest] at hrootRaw
  have hroot : C.bound + D.bound ≤ σ.bound := by
    simpa only [C, D] using hrootRaw

  have hDRaw := (ctx_bound_cut_le D (by decide +kernel) [0]
    (by decide +kernel) 2 (by decide) (by decide +kernel)).2
  rw [hDrest] at hDRaw
  have hDcut : E.bound + F.bound ≤ D.bound := by
    simpa only [E, F] using hDRaw

  have hFRaw := (ctx_bound_cut_le F (by decide +kernel) [1]
    (by decide +kernel) 1 (by decide) (by decide +kernel)).2
  rw [hFrest] at hFRaw
  have hFcut : G.bound + H.bound ≤ F.bound := by
    simpa only [G, H] using hFRaw

  have hC : C.bound = 5 := by
    set_option maxRecDepth 10000 in decide +kernel
  have hE : E.bound = 2 := by
    set_option maxRecDepth 10000 in decide +kernel
  have hG : G.bound = 1 := by
    set_option maxRecDepth 10000 in decide +kernel
  have hH : H.bound = 3 := by
    set_option maxRecDepth 10000 in decide +kernel
  have hF : 4 ≤ F.bound := by omega
  have hD : 6 ≤ D.bound := by omega
  have hbound : 11 ≤ σ.bound := by omega

  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, hbound, by decide +kernel⟩
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · simp [σ]
  · intro p l s hletter
    have hp : p < 7 := by
      by_contra hp
      rw [Ctx.Context.letterAt_of_length_le σ (by simp [σ]; omega)] at hletter
      cases hletter
    interval_cases p <;> simp [σ, Ctx.Context.letterAt] at hletter
    all_goals
      rcases hletter with ⟨rfl, rfl⟩
      decide


end ErdosSzekeres
