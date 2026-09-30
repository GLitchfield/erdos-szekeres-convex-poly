import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- Alternating single-run additivity (C3) from run contraction on parts of single-run contexts (hypothesis hpart, C1p) and external-letter deletion monotonicity for isolated children (hdel): the closed reduction ctx_bound_additive_single_run_alternating_of_run_contraction_and_deletion with its general-C1 hypothesis narrowed to what it uses, since every contraction there acts on a part of a single-run context (the run with one separator child removed). With the bridge ctx_bound_part_run_contraction_of_one_level_root this puts C3 on the root form of C1 alone (R7/R11).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_additive_prefix_suffix, ErdosSzekeres.ctx_bound_additive_sandwich_singleton_ends, ErdosSzekeres.ctx_base_child_letter_contraction
@consumer ErdosSzekeres.ctx_bound_additive_single_run_alternating -/
theorem ctx_bound_additive_single_run_alternating_of_part_contraction_and_deletion (hpart : ∀ (τ : Ctx.Context), τ.WellFormed → τ.numRuns ≤ 1 → ∀ (keep : List ℕ) (s : Ctx.Side) (m : ℕ), 1 ≤ m → m ≤ τ.k - 2 → ∀ (left right : List Ctx.Letter), (τ.part keep s m).word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right → (τ.part keep s m).bound = ({ τ.part keep s m with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).bound) (hdel : ∀ (τ : Ctx.Context), τ.WellFormed → (∀ p ∈ τ.childPositions, p + 1 ∉ τ.childPositions) → ∀ (left right : List Ctx.Letter) (lev : ℕ) (side : Ctx.Side), τ.word = left ++ [Ctx.Letter.ext lev side] ++ right → Ctx.Letter.ext lev side ∈ left ++ right → τ.bound ≤ ({ τ with word := left ++ right } : Ctx.Context).bound) (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (h2 : 2 ≤ σ.childPositions.length) (r : ℕ) (hr : r < 2) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : let keep := ((List.range σ.childPositions.length).filter (fun i => i % 2 = r)).map (fun i => σ.childPositions.getD i 0); (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  sorry

end ErdosSzekeres
