import ESBlueprint.B.CtxSingletonPartBoundEqThreshold

namespace ErdosSzekeres

/-- Inside-pair residual of the localized singleton-base and complement exchange X. All original legal root and cut hypotheses remain, with positive global axes, old chosen axis at least three, and p equal to one of the adjacent doubled child positions. Unit-axis and old-chosen-at-most-two cases are closed separately. Leaf monotonicity alone does not allocate the complement; the joint legal side/coupling exchange remains open.
@node
@ws B
@kind conjecture
@depends ErdosSzekeres.ctx_singleton_part_bound_eq_threshold
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange
@falsifier ctx_one_level_root_singleton_base_exchange_residuals.py -/
theorem ctx_one_level_root_singleton_base_exchange_inside_pair (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2) (ha2 : 2 ≤ a) (hu2 : 2 ≤ u) (side : Ctx.Side) (hchosen : 3 ≤ (match side with | Ctx.Side.lower => u | Ctx.Side.upper => a)) (left right : List Ctx.Letter) (hletters : ∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
  let σ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, maxima := [m] }
  let ρ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child] ++ right, maxima := [m] }
  let opposite : Ctx.Side → Ctx.Side := fun s => match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  2 ≤ σ.numRuns →
  ∀ p ∈ σ.childPositions, ∀ (s : Ctx.Side) (c : ℕ), 1 ≤ c → c ≤ k - 2 →
    (p = left.length ∨ p = left.length + 1) →
    let q := if p ≤ left.length then p else p - 1
    ∃ (t : Ctx.Side) (d : ℕ), 1 ≤ d ∧ d ≤ k - 2 ∧
      decomposableThreshold ((σ.part [p] s c).capLimit p p + 1) ((σ.part [p] s c).cupLimit p p + 1) k +
          (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound ≤
      decomposableThreshold ((ρ.part [q] t d).capLimit q q + 1) ((ρ.part [q] t d).cupLimit q q + 1) k +
          (ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) (opposite t) (k - 1 - d)).bound := by
  sorry

end ErdosSzekeres
