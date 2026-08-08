module

public import ErdosSzekeres.StructuralChargingSaturatedPredecessor

@[expose] public section

/-!
# Root-local form of the decomposable E3 transition

The outer hereditary state does not require summing payments from different
recursive call frames.  It is enough to prove one root-local transition: if
both children satisfy the outer cardinal bound and the parent avoids all three
target outcomes, then the parent satisfies the same bound.

For every positive threshold this root transition is equivalent to
`DecomposableStateUpper`.  Thus ancestor/descendant pivot reuse is irrelevant
unless the eventual proof of the root-local transition itself introduces a
tree-global sum.
-/

namespace ErdosSzekeres

/-- The exact root-local cardinal transition needed for the hereditary E3
state at parameters `(a,u,k)`. -/
def DecomposableRootTransitionUpper (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)},
    IsDecomposableOn χ lower → IsDecomposableOn χ upper →
      HasDeepBelowSplit χ lower upper →
        lower.card ≤ decomposableThreshold a u k →
          upper.card ≤ decomposableThreshold a u k →
            ¬ContainsCapSet χ (lower ∪ upper) a →
              ¬ContainsCupSet χ (lower ∪ upper) u →
                ¬ContainsStrongPolygonSet χ (lower ∪ upper) k →
                  (lower ∪ upper).card ≤ decomposableThreshold a u k

/-- Any root split larger than a common child bound contains an exact
`bound + 1` subsplit. Both restricted children remain nonempty and
decomposable, and the deep-below relation restricts to them. -/
theorem exists_critical_decomposable_subsplit
    {n bound : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hlower : IsDecomposableOn χ lower)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerBound : lower.card ≤ bound)
    (hupperBound : upper.card ≤ bound)
    (hlarge : bound < (lower ∪ upper).card) :
    ∃ lower' upper' : Finset (Fin n),
      lower' ⊆ lower ∧ upper' ⊆ upper ∧
        lower'.Nonempty ∧ upper'.Nonempty ∧
          IsDecomposableOn χ lower' ∧ IsDecomposableOn χ upper' ∧
            HasDeepBelowSplit χ lower' upper' ∧
              (lower' ∪ upper').card = bound + 1 := by
  classical
  have hcriticalCard : bound + 1 ≤ (lower ∪ upper).card := by omega
  obtain ⟨critical, hcriticalSub, hcriticalCardEq⟩ :=
    Finset.exists_subset_card_eq hcriticalCard
  let lower' := critical ∩ lower
  let upper' := critical ∩ upper
  have hlowerSub : lower' ⊆ lower := Finset.inter_subset_right
  have hupperSub : upper' ⊆ upper := Finset.inter_subset_right
  have hunion : lower' ∪ upper' = critical := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact (Finset.mem_inter.mp hq).1
      · exact (Finset.mem_inter.mp hq).1
    · intro hq
      rcases Finset.mem_union.mp (hcriticalSub hq) with hqLower | hqUpper
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hq, hqLower⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hq, hqUpper⟩)
  have hlowerNonempty : lower'.Nonempty := by
    by_contra hnot
    have hlowerEmpty : lower' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hcriticalUpper : critical ⊆ upper := by
      intro q hq
      have hqNotLower : q ∉ lower := by
        intro hqLower
        have hqLower' : q ∈ lower' := Finset.mem_inter.mpr ⟨hq, hqLower⟩
        rw [hlowerEmpty] at hqLower'
        simp at hqLower'
      exact (Finset.mem_union.mp (hcriticalSub hq)).resolve_left hqNotLower
    have hcardLe := Finset.card_le_card hcriticalUpper
    omega
  have hupperNonempty : upper'.Nonempty := by
    by_contra hnot
    have hupperEmpty : upper' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hcriticalLower : critical ⊆ lower := by
      intro q hq
      have hqNotUpper : q ∉ upper := by
        intro hqUpper
        have hqUpper' : q ∈ upper' := Finset.mem_inter.mpr ⟨hq, hqUpper⟩
        rw [hupperEmpty] at hqUpper'
        simp at hqUpper'
      exact (Finset.mem_union.mp (hcriticalSub hq)).resolve_right hqNotUpper
    have hcardLe := Finset.card_le_card hcriticalLower
    omega
  refine ⟨lower', upper', hlowerSub, hupperSub,
    hlowerNonempty, hupperNonempty, ?_, ?_, ?_, ?_⟩
  · exact hlower.subset hlowerSub hlowerNonempty
  · exact hupper.subset hupperSub hupperNonempty
  · exact hdeep.mono hlowerSub hupperSub
  · rw [hunion, hcriticalCardEq]

/-- Simultaneous retention of every canonical pivot turns the fixed-split
pivot injection into a numeric bound by the chosen core. -/
theorem hiddenGapSource_card_le_core_of_pivots_mem
    {n : ℕ} {lower upper core : Finset (Fin n)} {color : Turn}
    (hcore : ∀ source : HiddenGapSource lower upper color,
      source.enteringPivot ∈ core) :
    Fintype.card (HiddenGapSource lower upper color) ≤ core.card := by
  classical
  rw [← hiddenGapEnteringPivotSeed_card lower upper color]
  apply Finset.card_le_card
  intro pivot hpivot
  obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hpivot
  exact hcore source

/-- The saturated-predecessor dispatcher therefore returns not only one core
containing all current-root pivots, but the explicit root-local source-count
bound by that core. -/
theorem exists_saturatedPivotSlice_with_source_card_le_core
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
    (hsum : upperSlice.index + lowerSlice.index ≤ k - 1)
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
        Fintype.card (HiddenGapSource lower upper .left) ≤ slice.core.card ∧
          ∀ source : HiddenGapSource lower upper .left,
            source.enteringPivot ∈ slice.core) ∨
      ∃ slice : PublishedCapChildSlice a u k upper,
        Fintype.card (HiddenGapSource lower upper .right) ≤ slice.core.card ∧
          ∀ source : HiddenGapSource lower upper .right,
            source.enteringPivot ∈ slice.core := by
  rcases exists_saturatedPivotSlice_of_predecessors lowerSlice upperSlice
      ha hu hak huk hlowerNonempty hupperNonempty hlower hupper hdeep
      hsum hactive htotal hlowerOuter hupperOuter hpredecessors
      hnoCap hnoCup hnoStrong with hlowerBranch | hupperBranch
  · obtain ⟨slice, hcore⟩ := hlowerBranch
    exact Or.inl ⟨slice,
      hiddenGapSource_card_le_core_of_pivots_mem hcore, hcore⟩
  · obtain ⟨slice, hcore⟩ := hupperBranch
    exact Or.inr ⟨slice,
      hiddenGapSource_card_le_core_of_pivots_mem hcore, hcore⟩

/-- The source-count bound is not by itself a root cardinal contradiction at
the first higher gate. The exact `10+13` split and an eight-source/eight-core
payment satisfy all displayed scalar capacities. A further root-local
run-length or excess invariant is therefore necessary. -/
theorem saturated_source_core_capacity_arithmetic_is_consistent_at_488 :
    decomposableThreshold 4 8 8 + 1 = 23 ∧
      decomposableThreshold 3 8 8 + 1 = 8 ∧
      10 + 13 = decomposableThreshold 4 8 8 + 1 ∧
      8 ≤ decomposableThreshold 3 8 8 + 1 ∧
      10 ≤ decomposableThreshold 4 8 8 ∧
      13 ≤ decomposableThreshold 4 8 8 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top]

/-- The hereditary state immediately supplies its root-local transition. -/
theorem decomposableStateUpper_implies_rootTransitionUpper
    {a u k : ℕ} (hstate : DecomposableStateUpper a u k) :
    DecomposableRootTransitionUpper a u k := by
  intro n χ lower upper hlower hupper hdeep hlowerCard hupperCard
    hnoCap hnoCup hnoStrong
  by_contra hnot
  have hlarge : decomposableThreshold a u k < (lower ∪ upper).card :=
    Nat.lt_of_not_ge hnot
  rcases hstate (.split hlower hupper hdeep) hlarge with hcap | hcup | hstrong
  · exact hnoCap hcap
  · exact hnoCup hcup
  · exact hnoStrong hstrong

/-- Conversely, a root-local transition lifts by structural induction to the
full hereditary decomposable state.  Positivity of the threshold discharges
the singleton base case. -/
theorem rootTransitionUpper_implies_decomposableStateUpper
    {a u k : ℕ} (hthreshold : 1 ≤ decomposableThreshold a u k)
    (hroot : DecomposableRootTransitionUpper a u k) :
    DecomposableStateUpper a u k := by
  intro n χ s hdecomposable hlarge
  induction hdecomposable with
  | singleton i =>
      simp only [Finset.card_singleton] at hlarge
      omega
  | @split lower upper hlower hupper hdeep ihlower ihupper =>
      by_cases hlowerLarge : decomposableThreshold a u k < lower.card
      · rcases ihlower hlowerLarge with hcap | hcup | hstrong
        · exact Or.inl (FinsetPolygon.ContainsCapSet.mono hcap
            Finset.subset_union_left)
        · exact Or.inr (Or.inl (FinsetPolygon.ContainsCupSet.mono hcup
            Finset.subset_union_left))
        · exact Or.inr (Or.inr (FinsetPolygon.ContainsStrongPolygonSet.mono
            hstrong Finset.subset_union_left))
      by_cases hupperLarge : decomposableThreshold a u k < upper.card
      · rcases ihupper hupperLarge with hcap | hcup | hstrong
        · exact Or.inl (FinsetPolygon.ContainsCapSet.mono hcap
            Finset.subset_union_right)
        · exact Or.inr (Or.inl (FinsetPolygon.ContainsCupSet.mono hcup
            Finset.subset_union_right))
        · exact Or.inr (Or.inr (FinsetPolygon.ContainsStrongPolygonSet.mono
            hstrong Finset.subset_union_right))
      have hlowerCard : lower.card ≤ decomposableThreshold a u k :=
        Nat.le_of_not_gt hlowerLarge
      have hupperCard : upper.card ≤ decomposableThreshold a u k :=
        Nat.le_of_not_gt hupperLarge
      by_cases hcap : ContainsCapSet χ (lower ∪ upper) a
      · exact Or.inl hcap
      by_cases hcup : ContainsCupSet χ (lower ∪ upper) u
      · exact Or.inr (Or.inl hcup)
      by_cases hstrong : ContainsStrongPolygonSet χ (lower ∪ upper) k
      · exact Or.inr (Or.inr hstrong)
      have hcard := hroot hlower hupper hdeep hlowerCard hupperCard
        hcap hcup hstrong
      omega

/-- At every positive threshold, the root-local and hereditary formulations
are logically equivalent. -/
theorem rootTransitionUpper_iff_decomposableStateUpper
    {a u k : ℕ} (hthreshold : 1 ≤ decomposableThreshold a u k) :
    DecomposableRootTransitionUpper a u k ↔
      DecomposableStateUpper a u k := by
  constructor
  · exact rootTransitionUpper_implies_decomposableStateUpper hthreshold
  · exact decomposableStateUpper_implies_rootTransitionUpper

end ErdosSzekeres

end
