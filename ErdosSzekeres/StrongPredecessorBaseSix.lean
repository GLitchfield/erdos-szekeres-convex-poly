module

public import ErdosSzekeres.StrongPredecessorBaseSixThroughFourteen

@[expose] public section

/-!
# A finite closing interface for the predecessor-half theorem at six

The low-cardinality theorem already supplies the required predecessor-free
half support through fourteen vertices.  An exact strong-six cardinality ceiling
and the two remaining cardinalities therefore suffice to close the fixed
`k = 6` predecessor-half obligation.

This file proves only that composition.  It does not provide either of the two
remaining producers.
-/

namespace ErdosSzekeres

/-- The upper-bound half of the exact `ES(6) = 17` statement, expressed at the
sweep-coloring interface needed by the predecessor recurrence. -/
def StrongSixCardinalityCeiling : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ 6 →
    n ≤ 16

/-- The only ambient cardinalities not covered by the theorem through fourteen
once the exact strong-six ceiling is available. -/
def PredecessorHalfSubsetAtSixMiddle : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ 6 →
    15 ≤ n →
    n ≤ 16 →
    ∃ support : Finset (Fin n),
      ¬ContainsStrongPolygonSet χ support 5 ∧
      n ≤ 2 * support.card

/-- The exact-six ceiling and half-support on cardinalities fifteen and
sixteen close the fixed predecessor-half theorem at six. -/
theorem predecessorHalfSubsetAt_six_of_cardinalityCeiling_of_middle
    (hceiling : StrongSixCardinalityCeiling)
    (hmiddle : PredecessorHalfSubsetAtSixMiddle) :
    PredecessorHalfSubsetAt 6 := by
  intro n χ hrealizable hnoStrong
  by_cases hn : n ≤ 14
  · exact exists_predecessorHalfSubsetAtSix_of_card_le_fourteen
      hrealizable hnoStrong hn
  · exact hmiddle hrealizable hnoStrong (by omega)
      (hceiling hrealizable hnoStrong)

end ErdosSzekeres

end
