import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

/-- Kernel-certified finite obstruction to replacing exact global axes by capped axes and their signed difference, even with fixed geometry and identical source leaf limits. Two identical S,1Upper,S,S literal root geometries at k6/m1 and Lower source coupling3 have globals a4/u5 versus a5/u6, equal capped axes and signed axis difference, and equal source leaf cap1/cup3. Their full source values7/14 are individually rescued after contraction, but no common legal target side and coupling rescues both. The complementary contribution needs absolute numeric axis information. Ordinary kernel literal evaluation only; does not refute X or establish an unbounded selector rule.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange -/
theorem ctx_singleton_exchange_axis_difference_selector_counterexample :
  let σA : Ctx.Context := { a := 4, u := 5, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child], maxima := [1] }
  let σB : Ctx.Context := { a := 5, u := 6, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child], maxima := [1] }
  let ρA : Ctx.Context := { a := 4, u := 5, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper, Ctx.Letter.child], maxima := [1] }
  let ρB : Ctx.Context := { a := 5, u := 6, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper, Ctx.Letter.child], maxima := [1] }
  let value : Ctx.Context → ℕ → Ctx.Side → ℕ → ℕ := fun τ p s c =>
    decomposableThreshold ((τ.part [p] s c).capLimit p p + 1)
      ((τ.part [p] s c).cupLimit p p + 1) τ.k +
      (τ.part (τ.childPositions.filter (fun q => q ≠ p))
        (match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower)
        (τ.k - 1 - c)).bound
  min σA.a 3 = min σB.a 3 ∧
  min σA.u 3 = min σB.u 3 ∧
  σA.a + σB.u = σB.a + σA.u ∧
  σA.numRuns = 2 ∧ σB.numRuns = 2 ∧
  ρA.numRuns = 2 ∧ ρB.numRuns = 2 ∧
  σA.childPositions = [0, 2, 3] ∧ σB.childPositions = [0, 2, 3] ∧
  ρA.childPositions = [0, 2] ∧ ρB.childPositions = [0, 2] ∧
  (σA.part [2] Ctx.Side.lower 3).capLimit 2 2 = 1 ∧
  (σA.part [2] Ctx.Side.lower 3).cupLimit 2 2 = 3 ∧
  (σB.part [2] Ctx.Side.lower 3).capLimit 2 2 = 1 ∧
  (σB.part [2] Ctx.Side.lower 3).cupLimit 2 2 = 3 ∧
  value σA 2 Ctx.Side.lower 3 = 7 ∧
  value σB 2 Ctx.Side.lower 3 = 14 ∧
  value ρA 2 Ctx.Side.lower 2 = 7 ∧
  value ρB 2 Ctx.Side.lower 3 = 14 ∧
  (∀ (s : Ctx.Side) (d : ℕ), 1 ≤ d → d ≤ 4 →
    value ρA 2 s d < 7 ∨ value ρB 2 s d < 14) := by
  sorry

end ErdosSzekeres
