module

public import ErdosSzekeres.E3State455CNFGenerated
public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Kernel-checked `(4,5,5)` state certificate

The generated CNF bridge and LRAT proof rule out an eight-vertex coloring
which simultaneously satisfies the rank-three one-change law, has no
four-cap, has no five-cup, and has no strong five-set.
-/

namespace ErdosSzekeres

/-- Every eight-vertex coloring satisfying the rank-three one-change law has
a four-cap, a five-cup, or a strong five-set. -/
theorem exists_cap_four_or_cup_five_or_strong_five
    (χ : TripleColoring 8)
    (hallowed : ∀ (a b c d : Fin 8),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩)) :
    (∃ f : Fin 4 ↪o Fin 8, IsCap χ f) ∨
    (∃ f : Fin 5 ↪o Fin 8, IsCup χ f) ∨
    (∃ f : Fin 5 ↪o Fin 8, IsStrongPolygonOn χ f) := by
  by_contra h
  have hnoCap : ∀ f : Fin 4 ↪o Fin 8, ¬ IsCap χ f := by
    intro f hf
    exact h (Or.inl ⟨f, hf⟩)
  have hnoCup : ∀ f : Fin 5 ↪o Fin 8, ¬ IsCup χ f := by
    intro f hf
    exact h (Or.inr (Or.inl ⟨f, hf⟩))
  have hnoStrong : ∀ f : Fin 5 ↪o Fin 8, ¬ IsStrongPolygonOn χ f := by
    intro f hf
    exact h (Or.inr (Or.inr ⟨f, hf⟩))
  exact e3State455CNF_unsat χ
    (e3State455CNF_of_constraints χ hallowed hnoCap hnoCup hnoStrong)

/-- The kernel-checked `(4,5,5)` state holds for the whole abstract
decomposable class; no sweep-realizability assumption is needed. -/
theorem IsDecomposable.exists_cap_four_or_cup_five_or_strong_five
    {χ : TripleColoring 8} (h : IsDecomposable χ) :
    (∃ f : Fin 4 ↪o Fin 8, IsCap χ f) ∨
    (∃ f : Fin 5 ↪o Fin 8, IsCup χ f) ∨
    (∃ f : Fin 5 ↪o Fin 8, IsStrongPolygonOn χ f) := by
  apply ErdosSzekeres.exists_cap_four_or_cup_five_or_strong_five χ
  intro a b c d hab hbc hcd
  exact h.turnSequenceAllowed hab hbc hcd (by simp) (by simp) (by simp) (by simp)

end ErdosSzekeres

end
