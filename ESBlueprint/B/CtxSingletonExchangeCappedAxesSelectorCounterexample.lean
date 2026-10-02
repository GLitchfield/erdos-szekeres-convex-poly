import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

/-- Kernel-certified finite obstruction to a singleton-exchange selector which identifies global axes above three. Two identical literal three-child one-level-root geometries at k6, old Lower marker maximum1 and Lower source coupling4, with globals a4/u5 versus a5/u4, have matching capped axes and source value7. Each contracted root has a rescuing legal coupling, but no one target side and coupling rescues both. Thus the compressed selector must retain more numeric axis information. Checks full explicit threshold-plus-complement values and every legal target, not only leaf values; does not refute X or establish a universal finite-table rule.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange -/
theorem ctx_singleton_exchange_capped_axes_selector_counterexample :
  let σA : Ctx.Context := { a := 4, u := 5, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child, Ctx.Letter.child], maxima := [1] }
  let σB : Ctx.Context := { a := 5, u := 4, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child, Ctx.Letter.child], maxima := [1] }
  let ρA : Ctx.Context := { a := 4, u := 5, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child], maxima := [1] }
  let ρB : Ctx.Context := { a := 5, u := 4, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child], maxima := [1] }
  let value : Ctx.Context → ℕ → Ctx.Side → ℕ → ℕ := fun τ p s c =>
    decomposableThreshold ((τ.part [p] s c).capLimit p p + 1)
      ((τ.part [p] s c).cupLimit p p + 1) τ.k +
      (τ.part (τ.childPositions.filter (fun q => q ≠ p))
        (match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower)
        (τ.k - 1 - c)).bound
  min σA.a 3 = min σB.a 3 ∧
  min σA.u 3 = min σB.u 3 ∧
  σA.numRuns = 2 ∧ σB.numRuns = 2 ∧
  ρA.numRuns = 2 ∧ ρB.numRuns = 2 ∧
  σA.childPositions = [0, 2, 3] ∧ σB.childPositions = [0, 2, 3] ∧
  ρA.childPositions = [0, 2] ∧ ρB.childPositions = [0, 2] ∧
  value σA 2 Ctx.Side.lower 4 = 7 ∧
  value σB 2 Ctx.Side.lower 4 = 7 ∧
  value ρA 2 Ctx.Side.lower 2 = 9 ∧
  value ρB 2 Ctx.Side.lower 3 = 7 ∧
  (∀ (s : Ctx.Side) (d : ℕ), 1 ≤ d → d ≤ 4 →
    value ρA 2 s d < 7 ∨ value ρB 2 s d < 7) := by
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
    by decide +kernel, ?_⟩
  intro s d hd hd4
  have hdCases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases hdCases with rfl | rfl | rfl | rfl <;> cases s <;> decide +kernel


end ErdosSzekeres
