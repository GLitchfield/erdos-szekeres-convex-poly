import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Localized singleton-base versus complement-part exchange for a multi-run one-level root containing an adjacent child pair. Delete the second copy and map the chosen singleton position across that deletion. Its explicit threshold T plus the complement bound is dominated by the same mapped singleton in the shorter root at some orientation and admissible coupling. Both leaf values are explicit thresholds; no contraction or all-cut bound hypothesis is assumed. Finite R13 probes pass, but deriving C1r from this local exchange remains a separate open obligation.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root
@falsifier ctx_one_level_root_singleton_base_exchange.py -/
theorem ctx_one_level_root_singleton_base_exchange (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2) (side : Ctx.Side) (left right : List Ctx.Letter) (hletters : ∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
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
  sorry

end ErdosSzekeres
