module

public import ErdosSzekeres.CupCap

@[expose] public section

/-!
# The geometric frame in the Tóth--Valtr upper bound

This file isolates the exact interface supplied by the projective-normalization
step in the Tóth--Valtr proof.  The auxiliary swept point set has one fewer
point.  Cups transfer unchanged, while every cap extends through the selected
hull vertex and therefore gains one point.

Constructing this frame for every finite planar set in general position is the
geometric content of the argument; the cup--cap consumer is formalized
separately.
-/

namespace ErdosSzekeres

/-- The source-facing consequence of a Tóth--Valtr projective normalization.

The definition deliberately records both transfer directions used by the
published proof, rather than assuming its final convex-polygon conclusion. -/
def TothValtrFrame (s : Finset (Point 2)) : Prop :=
  ∃ q : Finset (Point 2), q.card + 1 = s.card ∧
    ∃ P : SweptPresentation q,
      (∀ {m : ℕ}, CupCap.HasCup P.configuration.tripleColoring m →
        ContainsConvexSubset s m) ∧
      (∀ {m : ℕ}, CupCap.HasCap P.configuration.tripleColoring m →
        ContainsConvexSubset s (m + 1))

end ErdosSzekeres

end
