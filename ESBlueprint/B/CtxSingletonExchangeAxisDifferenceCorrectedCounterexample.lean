import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

/-- Append-only corrected finite obstruction to selecting one common singleton-exchange cut from capped axes and exact axis difference. Identical literal S,1Upper,S,S geometry at k6/m1/Lower source3, globals(4,5)/(5,6), gives source7/14 and disjoint legal rescue choices. Actual source cap/cup data are(2,2)/(3,2), so this does not rule out selectors retaining actual leaf data. Conjoin the corrected complete literal certificate with the exact negation of the mistaken earlier candidate, whose asserted leafcap1/cup3 facts are false. The original declaration is preserved unchanged, not assumed in the proof. No refutation of X or universal selector claim; ordinary kernel evaluation only.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange -/
theorem ctx_singleton_exchange_axis_difference_corrected_counterexample :
  (
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
      (σA.part [2] Ctx.Side.lower 3).capLimit 2 2 = 2 ∧
      (σA.part [2] Ctx.Side.lower 3).cupLimit 2 2 = 2 ∧
      (σB.part [2] Ctx.Side.lower 3).capLimit 2 2 = 3 ∧
      (σB.part [2] Ctx.Side.lower 3).cupLimit 2 2 = 2 ∧
      value σA 2 Ctx.Side.lower 3 = 7 ∧
      value σB 2 Ctx.Side.lower 3 = 14 ∧
      value ρA 2 Ctx.Side.lower 2 = 7 ∧
      value ρB 2 Ctx.Side.lower 3 = 14 ∧
      (∀ (s : Ctx.Side) (d : ℕ), 1 ≤ d → d ≤ 4 →
        value ρA 2 s d < 7 ∨ value ρB 2 s d < 14)
  ) ∧ ¬ (
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
        value ρA 2 s d < 7 ∨ value ρB 2 s d < 14)
  ) := by
  constructor
  · dsimp only
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
      by decide +kernel, ?_⟩
    intro s d hd hd4
    have hdCases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
    rcases hdCases with rfl | rfl | rfl | rfl <;> cases s <;> decide +kernel
  · intro h
    dsimp only at h
    have hcap := h.2.2.2.2.2.2.2.2.2.2.2.1
    have hnot :
        ¬ ((({ a := 4, u := 5, k := 6, word := [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child], maxima := [1] } : Ctx.Context).part [2] Ctx.Side.lower 3).capLimit 2 2 = 1) := by
      decide +kernel
    exact hnot hcap


end ErdosSzekeres
