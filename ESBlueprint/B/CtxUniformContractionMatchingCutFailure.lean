import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- A concrete failure of corresponding-cut transport inside the uniform-separator class: shortening one repeated child run strictly decreases the cut sum obtained by removing the second child. Both contexts are well formed. The proof uses one witness cut and only small child calculations, ruling out direct same-cut induction for uniform contraction without requiring evaluation of the parent maxima.
@node
@ws B
@kind refutation
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_uniform_contraction_matching_cut_failure : let σ : Ctx.Context := ⟨5, 5, 6,
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper,
      Ctx.Letter.child, Ctx.Letter.child], [1]⟩
  let τ : Ctx.Context := { σ with word :=
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper, Ctx.Letter.child] }
  σ.WellFormed ∧ τ.WellFormed ∧
    (τ.part [0, 3] Ctx.Side.lower 1).bound + (τ.part [1] Ctx.Side.upper 4).bound <
      (σ.part [0, 3, 4] Ctx.Side.lower 1).bound + (σ.part [1] Ctx.Side.upper 4).bound := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp
    · intro p l s hletter
      have hp : p < 5 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le _ (show 5 ≤ p by omega)] at hletter
        cases hletter
      interval_cases p <;> simp [Ctx.Context.letterAt] at hletter
      rcases hletter with ⟨rfl, rfl⟩
      decide
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp
    · intro p l s hletter
      have hp : p < 4 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le _ (show 4 ≤ p by omega)] at hletter
        cases hletter
      interval_cases p <;> simp [Ctx.Context.letterAt] at hletter
      rcases hletter with ⟨rfl, rfl⟩
      decide
  · let σ : Ctx.Context := ⟨5, 5, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper,
        Ctx.Letter.child, Ctx.Letter.child], [1]⟩
    let τ : Ctx.Context := { σ with word :=
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper, Ctx.Letter.child] }
    let δ := σ.part [0, 3, 4] Ctx.Side.lower 1
    have hrun : 2 ≤ δ.numRuns := by decide
    have hblock : [0, 3] ∈ δ.blocks := by decide
    have hcut := (ctx_bound_cut_le δ hrun [0, 3] hblock 2 (by decide) (by decide)).1
    have hrest : δ.childPositions.filter (fun p ↦ decide (p ∉ [0, 3])) = [4] := by decide
    have hcomp : δ.k - 1 - 2 = 3 := by rfl
    have hleft : (δ.part [0, 3] Ctx.Side.lower 2).bound = 9 := by decide
    have hright : (δ.part [4] Ctx.Side.upper 3).bound = 3 := by decide
    rw [hrest, hcomp, hleft, hright] at hcut
    have hsmallLeft : (τ.part [0, 3] Ctx.Side.lower 1).bound = 9 := by decide
    have hsmallRight : (τ.part [1] Ctx.Side.upper 4).bound = 1 := by decide
    have hbigRight : (σ.part [1] Ctx.Side.upper 4).bound = 1 := by decide
    change (τ.part [0, 3] Ctx.Side.lower 1).bound +
        (τ.part [1] Ctx.Side.upper 4).bound < δ.bound +
          (σ.part [1] Ctx.Side.upper 4).bound
    omega

end ErdosSzekeres
