import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- ROOT-NF: a one-level root over child and ext 1 side has the bound of a word retaining the presence of both end markers, with one child per run and run count clamped at three on a global axis two, and at two otherwise. The axis-two exception preserves the diagnostic two-to-three-run drop. This alternate route implies C1r independently of N_root and X; no normal-form equality is assumed in its proof.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root
@falsifier ctx_one_level_root_normal_form.py
@measure number of child positions -/
theorem ctx_one_level_root_bound_normal_form (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k)
    (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2)
    (side : Ctx.Side) (word : List Ctx.Letter)
    (hletters : ∀ x ∈ word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
    let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
    let r := min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2)
    let marker := Ctx.Letter.ext 1 side
    let normalWord :=
      (if word.head? = some marker then [marker] else []) ++
      (List.replicate r Ctx.Letter.child).intersperse marker ++
      (if word.getLast? = some marker then [marker] else [])
    σ.bound = ({σ with word := normalWord} : Ctx.Context).bound := by
  sorry

end ErdosSzekeres
