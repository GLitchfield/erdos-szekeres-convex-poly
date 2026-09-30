import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- Single-run additivity from run contraction on parts of single-run contexts (hpart, C1p) and alternating additivity (halternating, C3): the closed R6 glue with its general-C1 hypothesis narrowed to what it uses (R7/R11).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_external_letter_contraction, ErdosSzekeres.ctx_base_child_letter_contraction
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_additive_single_run_of_part_contraction_and_alternating (hpart : ∀ (τ : Ctx.Context), τ.WellFormed → τ.numRuns ≤ 1 → ∀ (keep : List ℕ) (s : Ctx.Side) (m : ℕ), 1 ≤ m → m ≤ τ.k - 2 → ∀ (left right : List Ctx.Letter), (τ.part keep s m).word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right → (τ.part keep s m).bound = ({ τ.part keep s m with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).bound) (halternating : ∀ (τ : Ctx.Context), τ.WellFormed → τ.numRuns ≤ 1 → 2 ≤ τ.childPositions.length → ∀ (r : ℕ), r < 2 → ∀ (d : ℕ), 1 ≤ d → d ≤ τ.k - 2 → let keep := ((List.range τ.childPositions.length).filter (fun i => i % 2 = r)).map (fun i => τ.childPositions.getD i 0); (τ.part keep Ctx.Side.lower d).bound + (τ.part (τ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (τ.k - 1 - d)).bound ≤ τ.bound ∧ (τ.part keep Ctx.Side.upper (τ.k - 1 - d)).bound + (τ.part (τ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ τ.bound) (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  sorry

end ErdosSzekeres
