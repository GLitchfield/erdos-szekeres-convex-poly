import ESBlueprint.B.CtxBoundZeroOfUnitGlobalAxis
import ESBlueprint.B.CtxSingletonPartBoundEqThreshold

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Full localized singleton-base and complement exchange X for a one-level root when either global axis is at most one. Raw zero-bound vanishing and the exact singleton threshold identity make the source cut zero, so the original side and coupling are a valid choice. Removes the unit-axis boundary without a WellFormed hypothesis; positive-axis inside and multirun-complement cuts remain separate obligations.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_zero_of_unit_global_axis, ErdosSzekeres.ctx_singleton_part_bound_eq_threshold
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange
@falsifier ctx_one_level_root_singleton_base_exchange_residuals.py -/
theorem ctx_one_level_root_singleton_base_exchange_unit_axis (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2) (hunit : a ≤ 1 ∨ u ≤ 1) (side : Ctx.Side) (left right : List Ctx.Letter) (hletters : ∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
  let σ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, maxima := [m] }
  let ρ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child] ++ right, maxima := [m] }
  let opposite : Ctx.Side → Ctx.Side := fun s => match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  2 ≤ σ.numRuns →
  ∀ p ∈ σ.childPositions, ∀ (s : Ctx.Side) (c : ℕ), 1 ≤ c → c ≤ k - 2 →
    let q := if p ≤ left.length then p else p - 1
    ∃ (t : Ctx.Side) (d : ℕ), 1 ≤ d ∧ d ≤ k - 2 ∧
      decomposableThreshold ((σ.part [p] s c).capLimit p p + 1) ((σ.part [p] s c).cupLimit p p + 1) k +
          (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound ≤
      decomposableThreshold ((ρ.part [q] t d).capLimit q q + 1) ((ρ.part [q] t d).cupLimit q q + 1) k +
          (ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) (opposite t) (k - 1 - d)).bound := by
  classical
  dsimp only
  intro hruns p hp s c hc hck
  let σ : Context :=
    ⟨a, u, k, left ++ [Letter.child, Letter.child] ++ right, [m]⟩
  let opposite : Side → Side := fun t => match t with
    | .lower => .upper
    | .upper => .lower
  refine ⟨s, c, hc, hck, ?_⟩
  have hzeroCut :
      decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
          ((σ.part [p] s c).cupLimit p p + 1) k +
        (σ.part (σ.childPositions.filter (fun r => r ≠ p))
          (opposite s) (k - 1 - c)).bound = 0 := by
    rw [← ctx_singleton_part_bound_eq_threshold σ p hp s c,
      (ctx_bound_zero_of_unit_global_axis (σ.part [p] s c) hunit).2,
      (ctx_bound_zero_of_unit_global_axis
        (σ.part (σ.childPositions.filter (fun r => r ≠ p))
          (opposite s) (k - 1 - c)) hunit).2]
  rw [hzeroCut]
  exact Nat.zero_le _

end ErdosSzekeres
