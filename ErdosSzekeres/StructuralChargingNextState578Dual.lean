module

public import ErdosSzekeres.StructuralChargingNextState578

@[expose] public section

/-!
# Color-dual interface for the `(5,7,8)` singleton-upper tail

The unresolved `41+1` tail is exactly the color dual of a singleton-lower
gate with the cap and cup parameters exchanged.  This file records that
equivalence without claiming either gate is closed.
-/

namespace ErdosSzekeres

/-- The color-dual lower form of the `41+1` tail: one lower point lies below
a 41-vertex reservoir, with cap and cup parameters exchanged from `(5,7)` to
`(7,5)`. -/
def SingletonLowerColorDualGate578 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {reservoir : Finset (Fin n)},
    IsDecomposableOn χ reservoir →
    HasDeepBelowSplit χ {q} reservoir →
    reservoir.card = 41 →
    ¬ContainsCapSet χ ({q} ∪ reservoir) 7 →
    ¬ContainsCupSet χ ({q} ∪ reservoir) 5 →
    ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8 →
    False

/-- The singleton-upper `(5,7,8)` gate and its singleton-lower `(7,5,8)`
color-dual formulation are logically equivalent. -/
theorem singletonUpperCriticalGate578_iff_colorDualLower :
    SingletonUpperCriticalGate578 ↔ SingletonLowerColorDualGate578 := by
  constructor
  · intro hupper n χ q reservoir hreservoir hroot hcard
      hnoCap hnoCup hnoStrong
    apply hupper (χ := χ.dual) hreservoir.dual hroot.dual hcard
    · intro hcap
      have horiginal := containsCapSet_dual_iff.mp hcap
      exact hnoCup (by simpa [Finset.union_comm] using horiginal)
    · intro hcup
      have horiginal := containsCupSet_dual_iff.mp hcup
      exact hnoCap (by simpa [Finset.union_comm] using horiginal)
    · intro hstrong
      have horiginal := containsStrongPolygonSet_dual_iff.mp hstrong
      exact hnoStrong (by simpa [Finset.union_comm] using horiginal)
  · intro hdual n χ q lower hlower hroot hcard hnoCap hnoCup hnoStrong
    apply hdual (χ := χ.dual) hlower.dual hroot.dual hcard
    · intro hcap
      have horiginal := containsCapSet_dual_iff.mp hcap
      exact hnoCup (by simpa [Finset.union_comm] using horiginal)
    · intro hcup
      have horiginal := containsCupSet_dual_iff.mp hcup
      exact hnoCap (by simpa [Finset.union_comm] using horiginal)
    · intro hstrong
      have horiginal := containsStrongPolygonSet_dual_iff.mp hstrong
      exact hnoStrong (by simpa [Finset.union_comm] using horiginal)

end ErdosSzekeres

end
