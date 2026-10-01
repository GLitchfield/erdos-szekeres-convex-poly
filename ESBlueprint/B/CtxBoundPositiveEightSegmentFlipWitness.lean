import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

/-- A positive eight-child maximal-segment exchange witness with membership pattern 00110011, global parameters a=u=k=6, and mixed external maxima [1,2,1]. Flipping the interior pair [6,7] changes the original lower/upper partition value 5+4 to a value at least 9: the new two-child part has bound 3 and a three/three interval cut of the six-child part gives 3+3. This concrete certificate evaluates only contexts with at most four children and uses ctx_bound_cut_le for the six-child lower bound. It does not prove universal exchange or assert its exact six-child bound.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_positive_eight_segment_flip_witness :
    let σ : Ctx.Context := ⟨6, 6, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
       Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 2 Ctx.Side.upper,
       Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.child, Ctx.Letter.child], [1, 2, 1]⟩
    let keep : List ℕ := [3, 4, 9, 10]
    let segment : List ℕ := [6, 7]
    let next : List ℕ := [3, 4, 6, 7, 9, 10]
    let large := σ.part next Ctx.Side.lower 2
    let small := σ.part (σ.childPositions.filter (fun p ↦ p ∉ next)) Ctx.Side.upper 3
    σ.WellFormed ∧
      (σ.childPositions = [0, 1, 3, 4, 6, 7, 9, 10] ∧ σ.numRuns = 4 ∧
        σ.childPositions.filter (fun p ↦ p ∈ keep) ∉ σ.blocks ∧
        σ.childPositions.filter (fun p ↦ p ∉ keep) ∉ σ.blocks ∧
        σ.childPositions.map (fun p ↦ decide (p ∈ keep)) =
          [false, false, true, true, false, false, true, true] ∧
        σ.childPositions = [0, 1, 3, 4] ++ segment ++ [9, 10] ∧
        next = σ.childPositions.filter (fun p ↦
          (p ∈ keep ∧ p ∉ segment) ∨ (p ∉ keep ∧ p ∈ segment))) ∧
      ((σ.part keep Ctx.Side.lower 2).bound = 5 ∧
        (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep)) Ctx.Side.upper 3).bound = 4 ∧
        small.bound = 3 ∧
        (large.part [3, 4, 6] Ctx.Side.lower 2).bound = 3 ∧
        (large.part (large.childPositions.filter (fun p ↦ p ∉ [3, 4, 6]))
          Ctx.Side.upper 3).bound = 3) ∧
      (σ.part keep Ctx.Side.lower 2).bound +
        (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep)) Ctx.Side.upper 3).bound ≤
          large.bound + small.bound := by
  sorry

end ErdosSzekeres
