import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Singleton-cut attainment N_root for one-level roots: with maxima [m], uniform level-one letters, legal root globals and at least two runs, some singleton explicit threshold plus its complement-part bound attains the root bound. Only root contexts are asserted; arbitrary raw part histories are outside this statement. Narrows C1r together with the separately registered singleton-base exchange X. R14 optimal-block-size induction target, with closed three-child base.
@node
@ws B
@kind conjecture
@depends ErdosSzekeres.ctx_bound_attained_by_singleton_cut_of_le_three_children, ErdosSzekeres.ctx_singleton_part_bound_eq_threshold
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root
@falsifier ctx_one_level_root_singleton_attainment.py -/
theorem ctx_one_level_root_bound_attained_by_singleton_cut (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k)
    (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2)
    (side : Ctx.Side) (word : List Ctx.Letter)
    (hletters : ∀ x ∈ word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
  let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
  let opposite : Ctx.Side → Ctx.Side := fun s =>
    match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  2 ≤ σ.numRuns →
  ∃ p ∈ σ.childPositions, ∃ (s : Ctx.Side) (c : ℕ),
    1 ≤ c ∧ c ≤ k - 2 ∧
    σ.bound ≤ decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
      ((σ.part [p] s c).cupLimit p p + 1) k +
      (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound := by
  sorry

end ErdosSzekeres
