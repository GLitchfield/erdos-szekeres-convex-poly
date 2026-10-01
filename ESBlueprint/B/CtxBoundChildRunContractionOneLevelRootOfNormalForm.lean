import ESBlueprint.B.CtxNumRunsChildLetterContraction

namespace ErdosSzekeres

/-- Conditional C1r from ROOT-NF for the fixed legal one-level root globals, maximum and side. Adjacent child contraction preserves run count, head and last marker presence, so the two words have the same clamped normal word. ROOT-NF is an explicit universal word hypothesis; this proof does not import an open conjecture or assert unconditional contraction.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_num_runs_child_letter_contraction
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_bound_child_run_contraction_one_level_root_of_normal_form (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k)
    (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2)
    (side : Ctx.Side) (left right : List Ctx.Letter)
    (hletters : ∀ x ∈ left ++ right,
      x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side)
    (hNF : ∀ word : List Ctx.Letter,
      (∀ x ∈ word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) →
      let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
      let r := min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2)
      let marker := Ctx.Letter.ext 1 side
      let normalWord :=
        (if word.head? = some marker then [marker] else []) ++
        (List.replicate r Ctx.Letter.child).intersperse marker ++
        (if word.getLast? = some marker then [marker] else [])
      σ.bound = ({σ with word := normalWord} : Ctx.Context).bound) :
    ({a := a, u := u, k := k,
      word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right,
      maxima := [m]} : Ctx.Context).bound =
    ({a := a, u := u, k := k,
      word := left ++ [Ctx.Letter.child] ++ right,
      maxima := [m]} : Ctx.Context).bound := by
  classical
  let σ : Ctx.Context := ⟨a, u, k, left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, [m]⟩
  let ρ : Ctx.Context := ⟨a, u, k, left ++ [Ctx.Letter.child] ++ right, [m]⟩
  have hσletters : ∀ x ∈ σ.word,
      x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side := by
    intro x hx
    simp only [σ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | hx | hx) | hx
    · exact hletters x (List.mem_append_left _ hx)
    · exact Or.inl hx
    · exact Or.inl hx
    · exact hletters x (List.mem_append_right _ hx)
  have hρletters : ∀ x ∈ ρ.word,
      x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side := by
    intro x hx
    simp only [ρ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | hx) | hx
    · exact hletters x (List.mem_append_left _ hx)
    · exact Or.inl hx
    · exact hletters x (List.mem_append_right _ hx)
  have hruns : σ.numRuns = ρ.numRuns :=
    ctx_num_runs_child_letter_contraction σ left right rfl
  have hhead : σ.word.head? = ρ.word.head? := by
    cases left <;> simp [σ, ρ]
  have hlast : σ.word.getLast? = ρ.word.getLast? := by
    simp only [σ, ρ, List.getLast?_append]
    rfl
  have hσ := hNF σ.word hσletters
  have hρ := hNF ρ.word hρletters
  dsimp only at hσ hρ
  change σ.bound = ρ.bound
  rw [hσ, hρ]
  change (⟨a, u, k,
      (if σ.word.head? = some (Ctx.Letter.ext 1 side) then
          [Ctx.Letter.ext 1 side] else []) ++
        (List.replicate (min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2))
          Ctx.Letter.child).intersperse (Ctx.Letter.ext 1 side) ++
        (if σ.word.getLast? = some (Ctx.Letter.ext 1 side) then
          [Ctx.Letter.ext 1 side] else []), [m]⟩ : Ctx.Context).bound =
    (⟨a, u, k,
      (if ρ.word.head? = some (Ctx.Letter.ext 1 side) then
          [Ctx.Letter.ext 1 side] else []) ++
        (List.replicate (min ρ.numRuns (if a = 2 ∨ u = 2 then 3 else 2))
          Ctx.Letter.child).intersperse (Ctx.Letter.ext 1 side) ++
        (if ρ.word.getLast? = some (Ctx.Letter.ext 1 side) then
          [Ctx.Letter.ext 1 side] else []), [m]⟩ : Ctx.Context).bound
  rw [hruns, hhead, hlast]

end ErdosSzekeres
