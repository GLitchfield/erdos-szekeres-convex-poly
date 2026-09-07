import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

/-- Every partition for which either the kept child positions or their filtered complement is an interval block is covered by the interval recursion. Choosing the interval side as the recursive block and normalizing the double complement handles arbitrary block size and both orientations, leaving only partitions with neither side an interval for the multi-run exchange argument.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_interval_or_complement_le (σ : Ctx.Context) (hruns : 2 ≤ σ.numRuns) (keep : List ℕ) (hcut : keep ∈ σ.blocks ∨ σ.childPositions.filter (fun p ↦ p ∉ keep) ∈ σ.blocks) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  rcases hcut with hkeep | hrest
  · exact ctx_bound_cut_le σ hruns keep hkeep d hd hdk
  · let rest := σ.childPositions.filter (fun p ↦ p ∉ keep)
    change rest ∈ σ.blocks at hrest
    have hpart : ∀ s m,
        σ.part (σ.childPositions.filter (fun p ↦ p ∉ rest)) s m = σ.part keep s m := by
      intro s m
      unfold Ctx.Context.part
      congr 1
      apply List.map_congr_left
      intro p hp
      rcases hletter : σ.letterAt p with _ | ⟨level, side⟩
      · have hpchild : p ∈ σ.childPositions := by
          simp [Ctx.Context.childPositions, List.mem_range.1 hp, hletter]
        simp [rest, hpchild]
      · simp
    have h := ctx_bound_cut_le σ hruns rest hrest d hd hdk
    rw [hpart Ctx.Side.upper (σ.k - 1 - d), hpart Ctx.Side.lower d] at h
    constructor
    · simpa [rest, Nat.add_comm] using h.2
    · simpa [rest, Nat.add_comm] using h.1

end ErdosSzekeres
