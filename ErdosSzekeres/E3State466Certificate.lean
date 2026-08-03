module

public import ErdosSzekeres.E3State466CNFGenerated
public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Kernel-checked `(4,6,6)` state certificate

The generated CNF bridge and LRAT proof rule out a twelve-vertex coloring
which simultaneously satisfies the rank-three one-change law, has no
four-cap, has no six-cup, and has no strong six-set.  The first theorem below
states that result without exposing the generated encoding.  The second
specializes it to recursively decomposable colorings.
-/

namespace ErdosSzekeres

/-- Every twelve-vertex coloring satisfying the rank-three one-change law has
a four-cap, a six-cup, or a strong six-set. -/
theorem exists_cap_four_or_cup_six_or_strong_six
    (χ : TripleColoring 12)
    (hallowed : ∀ (a b c d : Fin 12),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩)) :
    (∃ f : Fin 4 ↪o Fin 12, IsCap χ f) ∨
    (∃ f : Fin 6 ↪o Fin 12, IsCup χ f) ∨
    (∃ f : Fin 6 ↪o Fin 12, IsStrongPolygonOn χ f) := by
  by_contra h
  have hnoCap : ∀ f : Fin 4 ↪o Fin 12, ¬ IsCap χ f := by
    intro f hf
    exact h (Or.inl ⟨f, hf⟩)
  have hnoCup : ∀ f : Fin 6 ↪o Fin 12, ¬ IsCup χ f := by
    intro f hf
    exact h (Or.inr (Or.inl ⟨f, hf⟩))
  have hnoStrong : ∀ f : Fin 6 ↪o Fin 12, ¬ IsStrongPolygonOn χ f := by
    intro f hf
    exact h (Or.inr (Or.inr ⟨f, hf⟩))
  exact e3State466CNF_unsat χ
    (e3State466CNF_of_constraints χ hallowed hnoCap hnoCup hnoStrong)

/-- The kernel-checked `(4,6,6)` state holds for the whole abstract
decomposable class; no sweep-realizability assumption is needed. -/
theorem IsDecomposable.exists_cap_four_or_cup_six_or_strong_six
    {χ : TripleColoring 12} (h : IsDecomposable χ) :
    (∃ f : Fin 4 ↪o Fin 12, IsCap χ f) ∨
    (∃ f : Fin 6 ↪o Fin 12, IsCup χ f) ∨
    (∃ f : Fin 6 ↪o Fin 12, IsStrongPolygonOn χ f) := by
  apply ErdosSzekeres.exists_cap_four_or_cup_six_or_strong_six χ
  intro a b c d hab hbc hcd
  exact h.turnSequenceAllowed hab hbc hcd (by simp) (by simp) (by simp) (by simp)

end ErdosSzekeres

end
