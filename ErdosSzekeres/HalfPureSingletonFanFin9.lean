module

public import ErdosSzekeres.ES5Certificate
public import ErdosSzekeres.HalfPureSingletonFan

@[expose] public section

/-!
# The OneChange strong-five theorem on nine vertices

This file bridges `OneChangeOn` and finite-set strong polygons to the existing
kernel-checked ES5 CNF certificate.  No new certificate or run-local
computation is used.
-/

namespace ErdosSzekeres

/-- Every one-change triple coloring on nine ordered vertices contains a
strong five-set. -/
theorem containsStrongFiveFinNine_of_oneChange
    (χ : TripleColoring 9) (hone : OneChangeOn χ Finset.univ) :
    ContainsStrongPolygonSet χ Finset.univ 5 := by
  by_contra hnoStrong
  have hallowed : ∀ (a b c d : Fin 9),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    exact hone hab hbc hcd (by simp) (by simp) (by simp) (by simp)
  have hnoEmbedding : ∀ f : Fin 5 ↪o Fin 9, ¬IsStrongPolygonOn χ f := by
    intro f hstrong
    apply hnoStrong
    refine ⟨Finset.univ.image f, Finset.subset_univ _, ?_,
      FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong⟩
    simpa using Finset.card_image_of_injective Finset.univ f.injective
  exact es5CNF_unsat χ
    (es5CNF_of_signotope_noStrong χ hallowed hnoEmbedding)

/-- The exact bounded singleton-fan conclusion on `Fin 9`.  This implication
is vacuous: its one-change and strong-five-free hypotheses contradict
`containsStrongFiveFinNine_of_oneChange`, so it supplies no fan witness in a
realizable premise state. -/
theorem halfPureSingletonFanAtFiveFinNine_of_oneChange
    (χ : TripleColoring 9) (hone : OneChangeOn χ Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :
    ∃ side : Finset (Fin 9), ∃ pivot : Fin 9,
      pivot ∉ side ∧
      9 ≤ 2 * side.card ∧
      ((HasDeepBelowSplit χ side {pivot} ∧
          ∀ polygon : Finset (Fin 9),
            polygon ⊆ side → polygon.card = 4 →
              IsStrongPolygonSet χ polygon → IsCupSet χ polygon) ∨
       (HasDeepBelowSplit χ {pivot} side ∧
          ∀ polygon : Finset (Fin 9),
            polygon ⊆ side → polygon.card = 4 →
              IsStrongPolygonSet χ polygon → IsCapSet χ polygon)) := by
  exact (hnoStrong (containsStrongFiveFinNine_of_oneChange χ hone)).elim

end ErdosSzekeres

end
