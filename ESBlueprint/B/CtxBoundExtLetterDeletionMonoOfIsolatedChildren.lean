import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- External-letter deletion monotonicity for contexts whose child letters are pairwise non-adjacent (every run a single child): deleting an external letter whose level keeps another letter cannot decrease the bound. The level-keeps-a-letter hypothesis is necessary (deleting the last letter of an upper level flips sideAt to lower and can add a join term). Proof route: replace the letter by an inert letter (ctx_bound_mono_of_marker_inclusion: limits and every fuel approximation only grow), then delete the inert letter by induction on fuel (limits unchanged, blocks and parts correspond); a merge to a single run can only produce two adjacent children, whose only cuts are prefix/suffix (ctx_bound_additive_prefix_suffix). Used with run contraction (C1) to shorten alternating partitions of a single run by two children (R7, runs/claude-comb-closedform-20260930). Evidence (compiled evaluator, diagnostic): 0 violations in 82,512 deletions over eight triples, 2-4 children (runs/claude-comb-closedform-20260930/d1/).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_mono_of_marker_inclusion, ErdosSzekeres.ctx_bound_additive_prefix_suffix, ErdosSzekeres.decomposableThreshold_mono
@consumer ErdosSzekeres.ctx_bound_additive_single_run_alternating -/
theorem ctx_bound_ext_letter_deletion_mono_of_isolated_children (σ : Ctx.Context) (hwf : σ.WellFormed) (hiso : ∀ p ∈ σ.childPositions, p + 1 ∉ σ.childPositions) (left right : List Ctx.Letter) (lev : ℕ) (side : Ctx.Side) (hword : σ.word = left ++ [Ctx.Letter.ext lev side] ++ right) (hother : Ctx.Letter.ext lev side ∈ left ++ right) : σ.bound ≤ ({ σ with word := left ++ right } : Ctx.Context).bound := by
  sorry

end ErdosSzekeres
