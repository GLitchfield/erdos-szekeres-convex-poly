import ESBlueprint.B.CtxBoundLeIffAllIntervalCutsLe

namespace ErdosSzekeres

/-- Every raw context with at least two child runs and positive full recursive bound has a proper interval block, legal coupling and orientation whose actual part-bound sum equals the full bound exactly. No well-formedness, global restrictions, history length or endpoint/singleton attainment hypothesis. Negate all-cut upper certificates at bound-1 and use closed cut domination. Supplies an unbounded constructive lower-witness starting point for positive maximal-segment exchange; no use of the refuted end-cut normal form.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_iff_all_interval_cuts_le, ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_positive_bound_attained_by_interval_cut (σ : Ctx.Context) (hruns : 2 ≤ σ.numRuns) (hpositive : 0 < σ.bound) :
∃ block ∈ σ.blocks, ∃ d : ℕ, 1 ≤ d ∧ d ≤ σ.k - 2 ∧
  (σ.bound =
    (σ.part block Ctx.Side.lower d).bound +
    (σ.part (σ.childPositions.filter (fun p => p ∉ block))
      Ctx.Side.upper (σ.k - 1 - d)).bound ∨
   σ.bound =
    (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound +
    (σ.part (σ.childPositions.filter (fun p => p ∉ block))
      Ctx.Side.lower d).bound) := by
  classical
  by_contra hnone
  have hcuts :
      ∀ block ∈ σ.blocks, ∀ d : ℕ, 1 ≤ d → d ≤ σ.k - 2 →
        (σ.part block Ctx.Side.lower d).bound +
          (σ.part (σ.childPositions.filter (fun p => p ∉ block))
            Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound - 1 ∧
        (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound +
          (σ.part (σ.childPositions.filter (fun p => p ∉ block))
            Ctx.Side.lower d).bound ≤ σ.bound - 1 := by
    intro block hb d hd hdk
    have hupper := ctx_bound_cut_le σ hruns block hb d hd hdk
    constructor
    · by_contra hbad
      have hu := hupper.1
      have heq : σ.bound =
          (σ.part block Ctx.Side.lower d).bound +
          (σ.part (σ.childPositions.filter (fun p => p ∉ block))
            Ctx.Side.upper (σ.k - 1 - d)).bound := by omega
      exact hnone ⟨block, hb, d, hd, hdk, Or.inl heq⟩
    · by_contra hbad
      have hu := hupper.2
      have heq : σ.bound =
          (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound +
          (σ.part (σ.childPositions.filter (fun p => p ∉ block))
            Ctx.Side.lower d).bound := by omega
      exact hnone ⟨block, hb, d, hd, hdk, Or.inr heq⟩
  have hbound : σ.bound ≤ σ.bound - 1 :=
    (ctx_bound_le_iff_all_interval_cuts_le σ hruns (σ.bound - 1)).2 hcuts
  omega

end ErdosSzekeres
