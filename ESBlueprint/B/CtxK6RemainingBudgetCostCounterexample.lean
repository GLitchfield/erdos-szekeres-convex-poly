import ESBlueprint.B.CtxBoundCutLe

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

/-- Exact R19 k6 counterexample to selecting a first child by pointwise remaining cup/cap budget loss. In SSS1L3L2LS at(5,5,6), maxima111, upper3 peels at p6 and p1 both have leaf capacity2. The end remainder preserves every ordered endpoint limit and has bound4; the middle loses cup budget but has bound at least6. Every legal end-child coupling gives sum at most7. Certified cut-tree lower bounds avoid evaluating the full parent maximum. The same literal context is separately certified satisfied; actual external-history realization is not asserted.
@node
@ws B
@kind formalization
@dangling-ok Resolves R19 proposed least-cost proof-route ambiguity by refuting the precise endpoint-budget-loss surrogate; preserves the run-geometry explanation with compiled evidence. -/
theorem ctx_k6_remaining_budget_cost_counterexample : let σ : Ctx.Context :=
    ⟨5, 5, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
       Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  let endRest := σ.part [0, 1, 2] Ctx.Side.lower 2
  let middleRest := σ.part [0, 2, 6] Ctx.Side.lower 2
  (∀ (p : ℕ), p ∈ [0, 1, 2] → ∀ (q : ℕ), q ∈ [0, 1, 2] → p ≤ q →
    endRest.cupLimit p q = σ.cupLimit p q ∧
      endRest.capLimit p q = σ.capLimit p q) ∧
  middleRest.cupLimit 0 0 < σ.cupLimit 0 0 ∧
  (σ.part [6] Ctx.Side.upper 3).bound = 2 ∧
  (σ.part [1] Ctx.Side.upper 3).bound = 2 ∧
  endRest.bound = 4 ∧
  6 ≤ middleRest.bound ∧
  (∀ d : ℕ, 1 ≤ d → d ≤ 4 →
    (σ.part [6] Ctx.Side.lower d).bound +
      (σ.part [0, 1, 2] Ctx.Side.upper (5 - d)).bound ≤ 7 ∧
    (σ.part [6] Ctx.Side.upper (5 - d)).bound +
      (σ.part [0, 1, 2] Ctx.Side.lower d).bound ≤ 7) := by
  let σ : Ctx.Context :=
    ⟨5, 5, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
       Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  let endRest := σ.part [0, 1, 2] Ctx.Side.lower 2
  let middleRest := σ.part [0, 2, 6] Ctx.Side.lower 2
  have hlimits : ∀ (p : ℕ), p ∈ [0, 1, 2] → ∀ (q : ℕ), q ∈ [0, 1, 2] → p ≤ q →
      endRest.cupLimit p q = σ.cupLimit p q ∧
        endRest.capLimit p q = σ.capLimit p q := by
    intro p hp q hq hpq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    all_goals first | omega | decide +kernel
  have hmiddle : 6 ≤ middleRest.bound := by
    let ρ := middleRest.part (middleRest.childPositions.filter (fun p => p ∉ [6]))
      Ctx.Side.upper 2
    have hρ : 2 ≤ ρ.bound := by
      have hle := (ctx_bound_cut_le ρ (by decide +kernel) [0] (by decide +kernel) 1
        (by decide) (by decide)).1
      have hvalue :
          (ρ.part [0] Ctx.Side.lower 1).bound +
            (ρ.part (ρ.childPositions.filter (fun p => p ∉ [0])) Ctx.Side.upper
              (ρ.k - 1 - 1)).bound = 2 := by decide +kernel
      rw [hvalue] at hle
      exact hle
    have hle := (ctx_bound_cut_le middleRest (by decide +kernel) [6] (by decide +kernel) 3
      (by decide) (by decide)).1
    have hleaf : (middleRest.part [6] Ctx.Side.lower 3).bound = 4 := by decide +kernel
    change (middleRest.part [6] Ctx.Side.lower 3).bound + ρ.bound ≤ middleRest.bound at hle
    rw [hleaf] at hle
    exact (Nat.add_le_add_left hρ 4).trans hle
  refine ⟨hlimits, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, hmiddle, ?_⟩
  intro d hd1 hd4
  interval_cases d <;> constructor <;> decide +kernel

end ErdosSzekeres
