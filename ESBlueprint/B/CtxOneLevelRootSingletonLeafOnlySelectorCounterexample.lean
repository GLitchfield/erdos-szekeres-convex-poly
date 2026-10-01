import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

/-- Kernel-certified inside-pair obstruction to choosing a singleton-exchange target orientation from only global and original/shortened leaf-limit data. Two legal literal one-level roots at a4/u5/k6/m1, old/source lower side and coupling4 have two runs, matching leaf cap3/cup1 before and after contraction, and source cut value6. The first shorter root is rescued by lower coupling2 and every upper cut is below6; the second is rescued by upper coupling2 and every lower cut is below6. Thus identical leaf/global inputs require opposite target orientations. Certifies retained R17 witnesses without refuting X or using native_decide.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange -/
theorem ctx_one_level_root_singleton_leaf_only_selector_counterexample :
  let σA : Ctx.Context := { a := 4, u := 5, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower], maxima := [1] }
  let σB : Ctx.Context := { a := 4, u := 5, k := 6, word := [Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child, Ctx.Letter.child], maxima := [1] }
  let ρA : Ctx.Context := { a := 4, u := 5, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower], maxima := [1] }
  let ρB : Ctx.Context := { a := 4, u := 5, k := 6, word := [Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child], maxima := [1] }
  let value : Ctx.Context → ℕ → Ctx.Side → ℕ → ℕ := fun τ p s c =>
    decomposableThreshold ((τ.part [p] s c).capLimit p p + 1)
      ((τ.part [p] s c).cupLimit p p + 1) τ.k +
      (τ.part (τ.childPositions.filter (fun q => q ≠ p))
        (match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower)
        (τ.k - 1 - c)).bound
  σA.numRuns = 2 ∧
  σB.numRuns = 2 ∧
  ρA.numRuns = 2 ∧
  ρB.numRuns = 2 ∧
  σA.childPositions = [0, 2, 3] ∧
  σB.childPositions = [1, 3, 4] ∧
  ρA.childPositions = [0, 2] ∧
  ρB.childPositions = [1, 3] ∧
  (σA.part [2] Ctx.Side.lower 4).capLimit 2 2 = 3 ∧
  (σA.part [2] Ctx.Side.lower 4).cupLimit 2 2 = 1 ∧
  (σB.part [3] Ctx.Side.lower 4).capLimit 3 3 = 3 ∧
  (σB.part [3] Ctx.Side.lower 4).cupLimit 3 3 = 1 ∧
  (ρA.part [2] Ctx.Side.lower 4).capLimit 2 2 = 3 ∧
  (ρA.part [2] Ctx.Side.lower 4).cupLimit 2 2 = 1 ∧
  (ρB.part [3] Ctx.Side.lower 4).capLimit 3 3 = 3 ∧
  (ρB.part [3] Ctx.Side.lower 4).cupLimit 3 3 = 1 ∧
  value σA 2 Ctx.Side.lower 4 = 6 ∧
  value σB 3 Ctx.Side.lower 4 = 6 ∧
  value ρA 2 Ctx.Side.lower 2 = 6 ∧
  value ρB 3 Ctx.Side.upper 2 = 6 ∧
  (∀ d : ℕ, 1 ≤ d → d ≤ 4 →
    value ρA 2 Ctx.Side.upper d < 6 ∧ value ρB 3 Ctx.Side.lower d < 6) := by
  dsimp only
  refine ⟨by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel, ?_⟩
  intro d hd hd4
  have hdCases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases hdCases with rfl | rfl | rfl | rfl <;> decide +kernel

end ErdosSzekeres
