module

public import ErdosSzekeres.StructuralChargingRootTransition

@[expose] public section

/-!
# Exact critical-root form of the structural-charging transition

The root-local transition may be reduced to excluding a split of exact
cardinality `decomposableThreshold a u k + 1`.  At such a split, the auxiliary
published-index sum required by the saturation arithmetic follows from the
strict predecessor states and the deep-below cup--cap gluing theorem; it does
not need to be assumed separately.
-/

namespace ErdosSzekeres

/-- The exact critical-root obstruction: no deep decomposable split of
threshold-plus-one vertices can have both children bounded while its union
avoids all three target outcomes. -/
def DecomposableCriticalRootImpossible (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)},
    IsDecomposableOn χ lower → IsDecomposableOn χ upper →
      HasDeepBelowSplit χ lower upper →
        lower.card ≤ decomposableThreshold a u k →
          upper.card ≤ decomposableThreshold a u k →
            (lower ∪ upper).card = decomposableThreshold a u k + 1 →
              ¬ContainsCapSet χ (lower ∪ upper) a →
                ¬ContainsCupSet χ (lower ∪ upper) u →
                  ¬ContainsStrongPolygonSet χ (lower ∪ upper) k → False

/-- A root transition excludes its exact critical obstruction. -/
theorem rootTransitionUpper_implies_criticalRootImpossible
    {a u k : ℕ} (hroot : DecomposableRootTransitionUpper a u k) :
    DecomposableCriticalRootImpossible a u k := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hcard hnoCap hnoCup hnoStrong
  have hbound := hroot hlower hupper hdeep hlowerBound hupperBound
    hnoCap hnoCup hnoStrong
  omega

/-- Conversely, exact critical-root impossibility proves the full root
transition by restricting any larger split to threshold plus one vertices. -/
theorem criticalRootImpossible_implies_rootTransitionUpper
    {a u k : ℕ} (hcritical : DecomposableCriticalRootImpossible a u k) :
    DecomposableRootTransitionUpper a u k := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hnoCap hnoCup hnoStrong
  by_contra hnot
  have hlarge : decomposableThreshold a u k < (lower ∪ upper).card :=
    Nat.lt_of_not_ge hnot
  obtain ⟨lower', upper', hlowerSub, hupperSub, hlowerNonempty,
      hupperNonempty, hlower', hupper', hdeep', hcard⟩ :=
    exists_critical_decomposable_subsplit hlower hupper hdeep
      hlowerBound hupperBound hlarge
  have hunionSub : lower' ∪ upper' ⊆ lower ∪ upper :=
    Finset.union_subset_union hlowerSub hupperSub
  have hlowerBound' : lower'.card ≤ decomposableThreshold a u k :=
    (Finset.card_le_card hlowerSub).trans hlowerBound
  have hupperBound' : upper'.card ≤ decomposableThreshold a u k :=
    (Finset.card_le_card hupperSub).trans hupperBound
  exact hcritical hlower' hupper' hdeep' hlowerBound' hupperBound' hcard
    (fun hcap ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub))
    (fun hcup ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub))
    (fun hstrong ↦ hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub))

/-- The arbitrary-size and exact critical-root formulations are equivalent. -/
theorem rootTransitionUpper_iff_criticalRootImpossible {a u k : ℕ} :
    DecomposableRootTransitionUpper a u k ↔
      DecomposableCriticalRootImpossible a u k := by
  exact ⟨rootTransitionUpper_implies_criticalRootImpossible,
    criticalRootImpossible_implies_rootTransitionUpper⟩

/-- The strict predecessor states force the published auxiliary indices to
have sum at most `k - 1`.  Otherwise the lower predecessor supplies a cup and
the upper predecessor supplies a cap whose deep-below union contains a strong
`k`-gon.  The outer state is not used. -/
theorem published_slice_indices_add_le_of_predecessors
    {n a u k : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (lowerSlice : PublishedChildSlice a u k lower)
    (upperSlice : PublishedCapChildSlice a u k upper)
    (hlowerNonempty : lower.Nonempty)
    (hupperNonempty : upper.Nonempty)
    (hlower : IsDecomposableOn χ lower)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerOuter : lower.card ≤ decomposableThreshold a u k)
    (hupperOuter : upper.card ≤ decomposableThreshold a u k)
    (hpredecessors : ∀ a' u', a' + u' < a + u →
      DecomposableStateUpper a' u' k)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) a)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) u)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) k) :
    upperSlice.index + lowerSlice.index ≤ k - 1 := by
  have ha : 1 ≤ a := by
    by_contra hnot
    have ha0 : a = 0 := by omega
    apply hnoCap
    refine ⟨∅, Finset.empty_subset _, by simp [ha0], ?_⟩
    intro t hi
    simp at hi
  have hu : 1 ≤ u := by
    by_contra hnot
    have hu0 : u = 0 := by omega
    apply hnoCup
    refine ⟨∅, Finset.empty_subset _, by simp [hu0], ?_⟩
    intro t hi
    simp at hi
  have hlowerIndexLt : lowerSlice.index < u :=
    lowerSlice.index_lt hu hlowerNonempty hlowerOuter
  have hupperIndexLt : upperSlice.index < a :=
    upperSlice.index_lt ha hupperNonempty hupperOuter
  have hlowerLarge :
      decomposableThreshold a lowerSlice.index k < lower.card := by
    rw [lowerSlice.index_eq]
    exact publishedChildIndex_threshold_lt hu hlowerNonempty.card_pos
  have hupperLarge :
      decomposableThreshold upperSlice.index u k < upper.card := by
    rw [upperSlice.index_eq]
    exact publishedCapChildIndex_threshold_lt ha hupperNonempty.card_pos
  have hlowerState : DecomposableStateUpper a lowerSlice.index k :=
    hpredecessors a lowerSlice.index (by omega)
  have hupperState : DecomposableStateUpper upperSlice.index u k :=
    hpredecessors upperSlice.index u (by omega)
  have hcup : ContainsCupSet χ lower lowerSlice.index := by
    rcases hlowerState hlower hlowerLarge with hcap | hcup | hstrong
    · exact False.elim (hnoCap
        (FinsetPolygon.ContainsCapSet.mono hcap Finset.subset_union_left))
    · exact hcup
    · exact False.elim (hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
          Finset.subset_union_left))
  have hcap : ContainsCapSet χ upper upperSlice.index := by
    rcases hupperState hupper hupperLarge with hcap | hcup | hstrong
    · exact hcap
    · exact False.elim (hnoCup
        (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_right))
    · exact False.elim (hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
          Finset.subset_union_right))
  by_contra hnot
  apply hnoStrong
  exact hdeep.containsStrongPolygonSet_of_containsCupCap hcup hcap (by omega)

/-- Consequently the saturated-predecessor dispatcher does not need the
auxiliary-index sum as an external hypothesis. -/
theorem exists_saturatedPivotSlice_of_predecessors_without_index_sum
    {n a u k : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (lowerSlice : PublishedChildSlice a u k lower)
    (upperSlice : PublishedCapChildSlice a u k upper)
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hlowerNonempty : lower.Nonempty)
    (hupperNonempty : upper.Nonempty)
    (hlower : IsDecomposableOn χ lower)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hactive : k + 4 ≤ a + u)
    (htotal : lower.card + upper.card = decomposableThreshold a u k + 1)
    (hlowerOuter : lower.card ≤ decomposableThreshold a u k)
    (hupperOuter : upper.card ≤ decomposableThreshold a u k)
    (hpredecessors : ∀ a' u', a' + u' < a + u →
      DecomposableStateUpper a' u' k)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) a)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) u)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) k) :
    (∃ slice : PublishedChildSlice a u k lower,
        ∀ source : HiddenGapSource lower upper .left,
          source.enteringPivot ∈ slice.core) ∨
      ∃ slice : PublishedCapChildSlice a u k upper,
        ∀ source : HiddenGapSource lower upper .right,
          source.enteringPivot ∈ slice.core := by
  have hsum := published_slice_indices_add_le_of_predecessors
    lowerSlice upperSlice hlowerNonempty hupperNonempty hlower hupper hdeep
    hlowerOuter hupperOuter hpredecessors hnoCap hnoCup hnoStrong
  exact exists_saturatedPivotSlice_of_predecessors lowerSlice upperSlice
    ha hu hak huk hlowerNonempty hupperNonempty hlower hupper hdeep
    hsum hactive htotal hlowerOuter hupperOuter hpredecessors
    hnoCap hnoCup hnoStrong

end ErdosSzekeres

end
