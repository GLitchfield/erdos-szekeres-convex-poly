import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A same-side strip exchange cannot in general preserve the interior block. In a well-formed 556 context, cutting a singleton interior block and then an end child gives total 12, while every end-first tree recutting that same interior block gives at most 10, with both end choices, both orientations at each cut, and every admissible coupling. The two new levels of the original residual are both lower. This refutes the fixed-block three-leaf exchange, not the unrestricted end-cut normal form.
@node
@ws B
@kind refutation
@consumer ErdosSzekeres.ctx_bound_attained_by_end_cut -/
theorem ctx_same_side_strip_fixed_block_counterexample : let σ : Ctx.Context := ⟨5, 5, 6,
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
      Ctx.Letter.child, Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1]⟩
  let R := σ.part [0, 3, 5] Ctx.Side.lower 1
  let before := (σ.part [1] Ctx.Side.upper 4).bound +
    (R.part [0] Ctx.Side.upper 4).bound + (R.part [3, 5] Ctx.Side.lower 1).bound
  let after (p : ℕ) (s t : Ctx.Side) (d e : ℕ) :=
    let opp := fun x : Ctx.Side ↦ match x with
      | Ctx.Side.lower => Ctx.Side.upper
      | Ctx.Side.upper => Ctx.Side.lower
    let maximum := fun x : Ctx.Side ↦ fun q : ℕ ↦ if x = Ctx.Side.lower then q else 5 - q
    let E := σ.part [p] s (maximum s d)
    let T := σ.part (σ.childPositions.filter (fun q ↦ q ≠ p)) (opp s) (maximum (opp s) d)
    E.bound + (T.part [1] t (maximum t e)).bound +
      (T.part (T.childPositions.filter (fun q ↦ q ≠ 1)) (opp t) (maximum (opp t) e)).bound
  σ.WellFormed ∧ σ.childPositions = [0, 1, 3, 5] ∧ σ.numRuns = 3 ∧
    (σ.part [1] Ctx.Side.upper 4).numRuns = 1 ∧
    (R.part [3, 5] Ctx.Side.lower 1).numRuns = 2 ∧ before = 12 ∧
    (∀ p ∈ [0, 5], ∀ d ∈ [1, 2, 3, 4], ∀ e ∈ [1, 2, 3, 4],
      ∀ s t : Ctx.Side, after p s t d e ≤ 10) := by
  dsimp only
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  · refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
    · simp
    · intro p l s hletter
      have hp : p < 6 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le _ (show 6 ≤ p by omega)] at hletter
        cases hletter
      interval_cases p <;> simp [Ctx.Context.letterAt] at hletter
      all_goals
        rcases hletter with ⟨rfl, rfl⟩
        decide
  · intro p hp d hd e he s t
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hd he
    rcases hp with rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl <;>
      rcases he with rfl | rfl | rfl | rfl <;>
      cases s <;> cases t <;> decide +kernel

end ErdosSzekeres
