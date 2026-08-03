module

public import ErdosSzekeres.E3State566CNFGenerated

@[expose] public section

/-!
# Kernel-checked `(5,6,6)` state certificate

The generated semantic bridge shows that any sixteen-vertex triple coloring
satisfying the rank-three one-change law and avoiding a five-cap, a six-cup,
and a strong six-set would satisfy the canonical DIMACS instance.  The
checkpointed LRAT proof derives a contradiction from that instance, with each
checkpoint theorem checked by the Lean kernel.
-/

namespace ErdosSzekeres

/-- Every sixteen-vertex coloring satisfying the rank-three one-change law has
a five-cap, a six-cup, or a strong six-set. -/
theorem exists_cap_five_or_cup_six_or_strong_six
    (χ : TripleColoring 16)
    (hallowed : ∀ (a b c d : Fin 16),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩)) :
    (∃ f : Fin 5 ↪o Fin 16, IsCap χ f) ∨
    (∃ f : Fin 6 ↪o Fin 16, IsCup χ f) ∨
    (∃ f : Fin 6 ↪o Fin 16, IsStrongPolygonOn χ f) := by
  by_contra h
  have hnoCap : ∀ f : Fin 5 ↪o Fin 16, ¬ IsCap χ f := by
    intro f hf
    exact h (Or.inl ⟨f, hf⟩)
  have hnoCup : ∀ f : Fin 6 ↪o Fin 16, ¬ IsCup χ f := by
    intro f hf
    exact h (Or.inr (Or.inl ⟨f, hf⟩))
  have hnoStrong : ∀ f : Fin 6 ↪o Fin 16, ¬ IsStrongPolygonOn χ f := by
    intro f hf
    exact h (Or.inr (Or.inr ⟨f, hf⟩))
  exact e3State566CNF_unsat χ
    (e3State566CNF_of_constraints χ hallowed hnoCap hnoCup hnoStrong)

end ErdosSzekeres

end
