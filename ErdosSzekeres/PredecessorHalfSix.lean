module

public import ErdosSzekeres.ES6Certificate
public import ErdosSzekeres.Fin15Anchored

@[expose] public section

/-!
# The fixed-six predecessor-half theorem, unconditionally

The strong-six cardinality ceiling comes from the ES(6) certificate; the
fifteen/sixteen middle comes from the anchored Fin15 certificate through
`AnchoredFin15Consumer.lean`; the theorem through fourteen vertices was
already available.  `StrongPredecessorBaseSix.lean` composes the three.
-/

namespace ErdosSzekeres

theorem strongSixCardinalityCeiling : StrongSixCardinalityCeiling := by
  intro n χ hreal hno
  exact strongSixCeiling_of_anchoredSeventeen anchoredSeventeenForcesStrongSix hreal hno

theorem predecessorHalfSubsetAt_six : PredecessorHalfSubsetAt 6 :=
  predecessorHalfSubsetAt_six_of_cardinalityCeiling_of_middle
    strongSixCardinalityCeiling predecessorHalfSubsetAtSixMiddle

end ErdosSzekeres

end
