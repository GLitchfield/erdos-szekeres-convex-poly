import ESBlueprint.B.CtxSameSideStripFixedBlockCounterexample

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Changing the second block repairs the certified same-side fixed-block obstruction. In the same well-formed 556 context, strip child 0 first and then child 5 at the opposite end; the resulting three-leaf tree has total 12, equal to the original interior-first tree, and lies below the first end cut and the parent bound. The earlier certificate rules out every replacement that recuts the original interior singleton. This certificate does not assert a general replacement theorem.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_attained_by_end_cut -/
theorem ctx_same_side_strip_changed_block_repair : let σ : Ctx.Context := ⟨5, 5, 6,
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
      Ctx.Letter.child, Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1]⟩
  let R := σ.part [0, 3, 5] Ctx.Side.lower 1
  let before := (σ.part [1] Ctx.Side.upper 4).bound +
    (R.part [0] Ctx.Side.upper 4).bound + (R.part [3, 5] Ctx.Side.lower 1).bound
  let E := σ.part [0] Ctx.Side.upper 3
  let T := σ.part [1, 3, 5] Ctx.Side.lower 2
  let after := E.bound + (T.part [5] Ctx.Side.upper 2).bound +
    (T.part [1, 3] Ctx.Side.lower 3).bound
  σ.WellFormed ∧ before = 12 ∧ after = 12 ∧
    before ≤ after ∧ after ≤ E.bound + T.bound ∧ E.bound + T.bound ≤ σ.bound := by
  dsimp only
  let σ : Ctx.Context := ⟨5, 5, 6,
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
      Ctx.Letter.child, Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1]⟩
  let T := σ.part [1, 3, 5] Ctx.Side.lower 2
  have hroot := ctx_bound_cut_le σ (by decide +kernel) [0] (by decide +kernel)
    2 (by decide) (by decide +kernel)
  have hsub := ctx_bound_cut_le T (by decide +kernel) [5] (by decide +kernel)
    3 (by decide) (by decide +kernel)
  have hcompRoot : σ.childPositions.filter (fun p => p ∉ [0]) = [1, 3, 5] := by decide +kernel
  have hcompSub : T.childPositions.filter (fun p => p ∉ [5]) = [1, 3] := by decide +kernel
  rw [hcompRoot] at hroot
  rw [hcompSub] at hsub
  have hwf := ctx_same_side_strip_fixed_block_counterexample.1
  refine ⟨hwf, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · decide +kernel
  · simpa only [Nat.add_assoc] using Nat.add_le_add_left hsub.2 (σ.part [0] Ctx.Side.upper 3).bound
  · exact hroot.2

end ErdosSzekeres
