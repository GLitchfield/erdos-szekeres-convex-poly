import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Extreme-run-end selector N_ends for N_root: in a legal one-level root with at least two runs, the root bound is attained by a singleton chosen among the first and last child of the first and last run. The explicit singleton threshold plus complement bound is unchanged. Boundary filters are evaluated on childPositions; successor word-end is explicit because letterAt defaults to child beyond the word. R16 item 1 approved by Gavin; diagnostic coordinator selector evidence only.
@node
@ws B
@kind conjecture
@depends ErdosSzekeres.ctx_bound_attained_by_singleton_cut_of_le_three_children, ErdosSzekeres.ctx_singleton_part_bound_eq_threshold
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut
@falsifier ctx_one_level_root_extreme_run_end_attainment.py -/
theorem ctx_one_level_root_bound_attained_by_extreme_run_end_singleton_cut (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k)
    (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2)
    (side : Ctx.Side) (word : List Ctx.Letter)
    (hletters : ∀ x ∈ word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
  let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
  let opposite : Ctx.Side → Ctx.Side := fun s =>
    match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  let ps := σ.childPositions
  let starts := ps.filter (fun p => p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child)
  let ends := ps.filter (fun p =>
    p + 1 = word.length ∨ σ.letterAt (p + 1) ≠ Ctx.Letter.child)
  2 ≤ σ.numRuns →
  ∃ p ∈ ps, p ∈ [(ps.head?).getD 0, (ends.head?).getD 0,
      (starts.getLast?).getD 0, (ps.getLast?).getD 0] ∧
    ∃ (s : Ctx.Side) (c : ℕ), 1 ≤ c ∧ c ≤ k - 2 ∧
      σ.bound ≤ decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
        ((σ.part [p] s c).cupLimit p p + 1) k +
        (σ.part (ps.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound := by
  sorry

end ErdosSzekeres
