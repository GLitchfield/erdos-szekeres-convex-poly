module

public import ErdosSzekeres.RankThreeBracket

@[expose] public section

/-!
# The Ringel nine-element rank-three chirotope

The increasing-triple signs below are extracted from the crossing sequences in
the public Java Oriented Matroids `Examples.ringel()` entry.  This module fixes
the exact representative and the complete reorientation-class restriction
semantics.  Its nonrealizability is proved separately.
-/

namespace ErdosSzekeres

noncomputable section

namespace RingelNine

/-- The twenty negative increasing triples in the authenticated Ringel
representative.  Every other increasing triple is positive. -/
def negativeTriples : Finset ((Fin 9 × Fin 9) × Fin 9) := {
  ((1, 2), 3), ((1, 2), 4), ((1, 2), 5), ((1, 2), 6), ((1, 2), 8),
  ((1, 5), 6), ((1, 5), 8), ((1, 7), 8), ((2, 7), 8), ((3, 5), 6),
  ((3, 5), 8), ((3, 7), 8), ((4, 5), 6), ((4, 5), 7), ((4, 5), 8),
  ((4, 6), 7), ((4, 6), 8), ((4, 7), 8), ((5, 7), 8), ((6, 7), 8)
}

/-- The authenticated Ringel increasing-triple coloring. -/
def coloring : TripleColoring 9 := fun t =>
  if ((t.i, t.j), t.k) ∈ negativeTriples then Turn.right else Turn.left

end RingelNine

/-- The full alternating sign function of the exact Ringel representative. -/
def ringelNineChirotope : Fin 9 → Fin 9 → Fin 9 → ℝ :=
  RingelNine.coloring.alternatingSign

/-- An increasingly selected ambient nine-set belongs to the full Ringel
reorientation class.  The internal equivalence permits arbitrary Ringel-label
permutation, independent element reorientation, and global sign. -/
def HasRingelNineRestrictionOn {n : ℕ} (chi : TripleColoring n)
    (f : Fin 9 ↪o Fin n) : Prop :=
  RankThreeReorientationEquivalent
    (chi.restrict f).alternatingSign ringelNineChirotope

/-- A realizable Ringel-class restriction would realize the exact fixed Ringel
representative by homogeneous rank-three vectors. -/
theorem HasRingelNineRestrictionOn.ringelNine_vectorRealizable {n : ℕ}
    {chi : TripleColoring n} {f : Fin 9 ↪o Fin n}
    (hchi : IsSweepRealizable chi)
    (hrestriction : HasRingelNineRestrictionOn chi f) :
    RankThreeVectorRealizable ringelNineChirotope := by
  have hrestricted := (hchi.restrict f).rankThreeVectorRealizable
  exact hrestricted.of_reorientationEquivalent hrestriction

/-- Conditional form of the public exclusion theorem.  It isolates the exact
finite certificate required from the companion nonrealizability module. -/
theorem IsSweepRealizable.noRingelNineRestrictionOn_of_nonrealizable {n : ℕ}
    {chi : TripleColoring n} (hchi : IsSweepRealizable chi)
    (hRingel : ¬RankThreeVectorRealizable ringelNineChirotope)
    (f : Fin 9 ↪o Fin n) :
    ¬HasRingelNineRestrictionOn chi f := by
  intro hrestriction
  exact hRingel (hrestriction.ringelNine_vectorRealizable hchi)

end
end ErdosSzekeres

end
