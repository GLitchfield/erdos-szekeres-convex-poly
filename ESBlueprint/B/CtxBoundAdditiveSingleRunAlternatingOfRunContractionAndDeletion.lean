import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- Conditional alternating single-run additivity (C3) from explicit run contraction under level-one spans (C1, hypothesis hcontract) and external-letter deletion monotonicity for isolated children (hypothesis hdel, the statement of ctx_bound_ext_letter_deletion_mono_of_isolated_children). Induction on the run length n: n = 2 is ctx_bound_additive_prefix_suffix, n = 3 is ctx_bound_additive_sandwich_singleton_ends; for n >= 4 delete the second and third children: in each part delete the separator between two teeth (hdel; the level keeps a letter) and contract the doubled tooth (hcontract), which yields the parts of the alternating partition of the run shortened by two, with the same base (ctx_base_child_letter_contraction). No proof of either hypothesis is asserted (R7, runs/claude-comb-closedform-20260930). Evidence for the shortening step (compiled evaluator, diagnostic): V(n) <= V(n-2) in all 7,040 root-level comparisons, k = 5..8.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_additive_prefix_suffix, ErdosSzekeres.ctx_bound_additive_sandwich_singleton_ends, ErdosSzekeres.ctx_base_child_letter_contraction
@consumer ErdosSzekeres.ctx_bound_additive_single_run_alternating -/
theorem ctx_bound_additive_single_run_alternating_of_run_contraction_and_deletion (hcontract : ∀ (τ : Ctx.Context), τ.WellFormed → ∀ (side : Ctx.Side) (left right : List Ctx.Letter), τ.word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right → (∀ i ∈ τ.childPositions, ∀ j ∈ τ.childPositions, ∀ l : ℕ, i < l → l < j → τ.letterAt l = Ctx.Letter.child ∨ τ.letterAt l = Ctx.Letter.ext 1 side) → τ.bound = ({ τ with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).bound) (hdel : ∀ (τ : Ctx.Context), τ.WellFormed → (∀ p ∈ τ.childPositions, p + 1 ∉ τ.childPositions) → ∀ (left right : List Ctx.Letter) (lev : ℕ) (side : Ctx.Side), τ.word = left ++ [Ctx.Letter.ext lev side] ++ right → Ctx.Letter.ext lev side ∈ left ++ right → τ.bound ≤ ({ τ with word := left ++ right } : Ctx.Context).bound) (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (h2 : 2 ≤ σ.childPositions.length) (r : ℕ) (hr : r < 2) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : let keep := ((List.range σ.childPositions.length).filter (fun i => i % 2 = r)).map (fun i => σ.childPositions.getD i 0); (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  sorry

end ErdosSzekeres
