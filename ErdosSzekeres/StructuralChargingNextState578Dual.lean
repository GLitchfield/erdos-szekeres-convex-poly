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

/-- Exact-size restriction of the color-dual lower gate.  This is the
32-vertex local obligation actually needed inside the `41+1` tail. -/
def SingletonLowerColorDualGate578At32 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {reservoir : Finset (Fin n)},
    IsDecomposableOn χ reservoir →
    HasDeepBelowSplit χ {q} reservoir →
    reservoir.card = 32 →
    ¬ContainsCapSet χ ({q} ∪ reservoir) 7 →
    ¬ContainsCupSet χ ({q} ∪ reservoir) 5 →
    ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8 →
    False

/-- A 32-vertex proof of the swapped `(7,5,8)` singleton-lower gate closes
the original `41+1` singleton-upper tail: restrict the 41-vertex reservoir to
32 vertices and then apply color duality. -/
theorem singletonUpperCriticalGate578_of_colorDualLowerAt32
    (hdual32 : SingletonLowerColorDualGate578At32) :
    SingletonUpperCriticalGate578 := by
  intro n χ q lower hlower hroot hcard hnoCap hnoCup hnoStrong
  obtain ⟨reservoir, hreservoirLower, hreservoirCard⟩ :=
    Finset.exists_subset_card_eq (show 32 ≤ lower.card by omega)
  have hreservoirNonempty : reservoir.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hreservoir : IsDecomposableOn χ reservoir :=
    hlower.subset hreservoirLower hreservoirNonempty
  have hrootRestricted : HasDeepBelowSplit χ lower {q} := hroot
  have hdualRoot : HasDeepBelowSplit χ.dual {q} reservoir :=
    hrootRestricted.dual.mono Finset.Subset.rfl hreservoirLower
  have hunionSub : reservoir ∪ {q} ⊆ lower ∪ {q} :=
    Finset.union_subset_union hreservoirLower Finset.Subset.rfl
  apply hdual32 (χ := χ.dual) hreservoir.dual hdualRoot hreservoirCard
  · intro hcap
    have horiginal := containsCapSet_dual_iff.mp hcap
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono
      (by simpa [Finset.union_comm] using horiginal) hunionSub)
  · intro hcup
    have horiginal := containsCupSet_dual_iff.mp hcup
    exact hnoCap (FinsetPolygon.ContainsCapSet.mono
      (by simpa [Finset.union_comm] using horiginal) hunionSub)
  · intro hstrong
    have horiginal := containsStrongPolygonSet_dual_iff.mp hstrong
    exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono
      (by simpa [Finset.union_comm] using horiginal) hunionSub)

/-- The exact 32-vertex swapped gate inherits a dense four-cup reservoir:
every decomposable 23-vertex restriction contains a four-cup.  This is the
color-dual counterpart of the cap-density input used by the singleton-lower
route; unlike that route, no common straddling-cut theorem is claimed. -/
theorem containsCupFour_of_colorDualLower_large_subset_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir s : Finset (Fin n)}
    (hs : IsDecomposableOn χ s) (hcard : 23 ≤ s.card)
    (hsub : s ⊆ reservoir)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ContainsCupSet χ s 4 := by
  have hnoCupDual : ¬ContainsCupSet χ.dual ({q} ∪ reservoir) 7 := by
    intro hcup
    exact hnoCap (containsCupSet_dual_iff.mp hcup)
  have hnoStrongDual :
      ¬ContainsStrongPolygonSet χ.dual ({q} ∪ reservoir) 8 := by
    intro hstrong
    exact hnoStrong (containsStrongPolygonSet_dual_iff.mp hstrong)
  have hcapDual := containsCapFour_of_decomposable_large_subset_at_578
    (χ := χ.dual) (q := q) (upper := reservoir) hs.dual hcard hsub
    hnoCupDual hnoStrongDual
  exact containsCapSet_dual_iff.mp hcapDual

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
