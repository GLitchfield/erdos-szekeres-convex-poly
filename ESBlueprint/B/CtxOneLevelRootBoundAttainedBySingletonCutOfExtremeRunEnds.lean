import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Direct pointwise weakening from the extreme-run-end selector N_ends to N_root for legal one-level roots. Takes exactly the selector conclusion as hypothesis hends and discards membership in its four candidates, preserving every root parameter and the explicit singleton-threshold plus complement-bound inequality. No open theorem is a proof dependency; a future proof of N_ends supplies hends at each root. R16 item 1 approved by Gavin.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_one_level_root_bound_attained_by_singleton_cut_of_extreme_run_ends (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k)
    (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2)
    (side : Ctx.Side) (word : List Ctx.Letter)
    (hletters : ∀ x ∈ word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side)
    (hends :
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
            (σ.part (ps.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound) :
  let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
  let opposite : Ctx.Side → Ctx.Side := fun s =>
    match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  2 ≤ σ.numRuns →
  ∃ p ∈ σ.childPositions, ∃ (s : Ctx.Side) (c : ℕ),
    1 ≤ c ∧ c ≤ k - 2 ∧
    σ.bound ≤ decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
      ((σ.part [p] s c).cupLimit p p + 1) k +
      (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound := by
  dsimp only at hends ⊢
  intro hruns
  obtain ⟨p, hp, _, hcut⟩ := hends hruns
  exact ⟨p, hp, hcut⟩

end ErdosSzekeres
