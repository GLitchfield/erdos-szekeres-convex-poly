module

public import ErdosSzekeres.StructuralChargingResidualBudget

@[expose] public section

/-!
# One-sided excess contracts at a critical root

The saturated-branch dispatcher supplies one selected published core containing
all compatible hidden-gap pivots.  The exact visible/hidden partition exposes
two logically separate geometric obligations:

* a visible-core bound, which makes the unselected residual no larger than the
  compatible hidden-gap family; and
* residual strictness, which says target avoidance makes that same residual
  strictly larger than the hidden-gap family.

This file proves that the two obligations contradict each other and connects
that contradiction to exact critical-root impossibility.  It does not prove
either geometric obligation.
-/

namespace ErdosSzekeres

/-- All root data available after reducing to an exact critical split and
choosing one published slice in each child. -/
structure CriticalRootSliceContext (a u k : ℕ) where
  n : ℕ
  χ : TripleColoring n
  lowerChild : Finset (Fin n)
  upperChild : Finset (Fin n)
  lowerSlice : PublishedChildSlice a u k lowerChild
  upperSlice : PublishedCapChildSlice a u k upperChild
  lowerNonempty : lowerChild.Nonempty
  upperNonempty : upperChild.Nonempty
  lowerDecomposable : IsDecomposableOn χ lowerChild
  upperDecomposable : IsDecomposableOn χ upperChild
  deep : HasDeepBelowSplit χ lowerChild upperChild
  total : lowerChild.card + upperChild.card =
    decomposableThreshold a u k + 1
  lowerOuter : lowerChild.card ≤ decomposableThreshold a u k
  upperOuter : upperChild.card ≤ decomposableThreshold a u k
  predecessors : ∀ a' u', a' + u' < a + u →
    DecomposableStateUpper a' u' k
  noCap : ¬ContainsCapSet χ (lowerChild ∪ upperChild) a
  noCup : ¬ContainsCupSet χ (lowerChild ∪ upperChild) u
  noStrong : ¬ContainsStrongPolygonSet χ (lowerChild ∪ upperChild) k

namespace CriticalRootSliceContext

variable {a u k : ℕ} (context : CriticalRootSliceContext a u k)

/-- The saturated lower branch has a reselected lower core containing every
left-colored hidden-gap pivot. -/
def HasLowerSelectedPivotCore : Prop :=
  PublishedSaturatedBranch.Valid a u k context.upperSlice.index
      context.lowerSlice.index .lower ∧
    ∃ slice : PublishedChildSlice a u k context.lowerChild,
      slice.index = context.lowerSlice.index ∧
        ∀ source : HiddenGapSource context.lowerChild context.upperChild .left,
          source.enteringPivot ∈ slice.core

/-- The saturated upper branch has a reselected upper core containing every
right-colored hidden-gap pivot. -/
def HasUpperSelectedPivotCore : Prop :=
  PublishedSaturatedBranch.Valid a u k context.upperSlice.index
      context.lowerSlice.index .upper ∧
    ∃ slice : PublishedCapChildSlice a u k context.upperChild,
      slice.index = context.upperSlice.index ∧
        ∀ source : HiddenGapSource context.lowerChild context.upperChild .right,
          source.enteringPivot ∈ slice.core

/-- The branch-selection conclusion returned by the strict predecessors. -/
def HasSelectedPivotCore : Prop :=
  context.HasLowerSelectedPivotCore ∨ context.HasUpperSelectedPivotCore

/-- Candidate root invariant: on the side opposite the selected pivot core,
visible child adjacencies fit inside that child's published threshold core. -/
def OneSidedVisibleCoreBound : Prop :=
  (context.HasLowerSelectedPivotCore →
      Fintype.card
          (VisibleUpperAdjacency context.lowerChild context.upperChild) ≤
        decomposableThreshold context.upperSlice.index u k) ∧
    (context.HasUpperSelectedPivotCore →
      Fintype.card
          (VisibleLowerAdjacency context.lowerChild context.upperChild) ≤
        decomposableThreshold a context.lowerSlice.index k)

/-- Candidate geometric consumer: if a branch retains every compatible pivot
while the parent avoids all targets, then the opposite discarded residual must
strictly exceed the compatible hidden-gap family. -/
def OneSidedResidualStrictness : Prop :=
  (context.HasLowerSelectedPivotCore →
      Fintype.card
          (HiddenGapSource context.lowerChild context.upperChild .left) <
        (context.upperChild \ context.upperSlice.core).card) ∧
    (context.HasUpperSelectedPivotCore →
      Fintype.card
          (HiddenGapSource context.lowerChild context.upperChild .right) <
        (context.lowerChild \ context.lowerSlice.core).card)

/-- The exact partition turns a visible-core bound into the negation of
residual strictness on whichever saturated branch the dispatcher selects. -/
theorem false_of_visibleCoreBound_and_residualStrictness
    (hselected : context.HasSelectedPivotCore)
    (hvisible : context.OneSidedVisibleCoreBound)
    (hstrict : context.OneSidedResidualStrictness) : False := by
  rcases hselected with hlowerSelected | hupperSelected
  · have hvisibleUpper := hvisible.1 hlowerSelected
    have hpaid :
        (context.upperChild \ context.upperSlice.core).card ≤
          Fintype.card
            (HiddenGapSource context.lowerChild context.upperChild .left) :=
      (upperSlice_remainder_le_hidden_iff_visible_le_threshold
        context.upperSlice context.upperNonempty).mpr hvisibleUpper
    exact (Nat.not_lt_of_ge hpaid) (hstrict.1 hlowerSelected)
  · have hvisibleLower := hvisible.2 hupperSelected
    have hpaid :
        (context.lowerChild \ context.lowerSlice.core).card ≤
          Fintype.card
            (HiddenGapSource context.lowerChild context.upperChild .right) :=
      (lowerSlice_remainder_le_hidden_iff_visible_le_threshold
        context.lowerSlice context.lowerNonempty).mpr hvisibleLower
    exact (Nat.not_lt_of_ge hpaid) (hstrict.2 hupperSelected)

end CriticalRootSliceContext

/-- If the two one-sided geometric contracts hold for every exact critical
context, strict predecessor states close the exact critical-root obstruction.
This is the formal consumer for future proofs or falsifiers of those contracts.
-/
theorem criticalRootImpossible_of_oneSided_excess_contracts
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hactive : k + 4 ≤ a + u)
    (hpredecessors : ∀ a' u', a' + u' < a + u →
      DecomposableStateUpper a' u' k)
    (hvisible : ∀ context : CriticalRootSliceContext a u k,
      context.OneSidedVisibleCoreBound)
    (hstrict : ∀ context : CriticalRootSliceContext a u k,
      context.OneSidedResidualStrictness) :
    DecomposableCriticalRootImpossible a u k := by
  intro n χ lower upper hlower hupper hdeep hlowerOuter hupperOuter
    hcard hnoCap hnoCup hnoStrong
  classical
  obtain ⟨lowerSlice⟩ :=
    exists_publishedChildSlice (a := a) (u := u) (k := k)
      (by omega) hlower.nonempty
  obtain ⟨upperSlice, _⟩ :=
    exists_publishedCapChildSlice_core_superset
      (a := a) (u := u) (k := k) (child := upper) (seed := ∅)
      (by omega) hupper.nonempty (by simp) (by simp)
  have htotal : lower.card + upper.card =
      decomposableThreshold a u k + 1 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint]
    exact hcard
  let context : CriticalRootSliceContext a u k :=
    { n := n
      χ := χ
      lowerChild := lower
      upperChild := upper
      lowerSlice := lowerSlice
      upperSlice := upperSlice
      lowerNonempty := hlower.nonempty
      upperNonempty := hupper.nonempty
      lowerDecomposable := hlower
      upperDecomposable := hupper
      deep := hdeep
      total := htotal
      lowerOuter := hlowerOuter
      upperOuter := hupperOuter
      predecessors := hpredecessors
      noCap := hnoCap
      noCup := hnoCup
      noStrong := hnoStrong }
  have hsum : upperSlice.index + lowerSlice.index ≤ k - 1 :=
    published_slice_indices_add_le_of_predecessors lowerSlice upperSlice
      hlower.nonempty hupper.nonempty hlower hupper hdeep hlowerOuter
      hupperOuter hpredecessors hnoCap hnoCup hnoStrong
  have hselected : context.HasSelectedPivotCore := by
    obtain ⟨branch, hvalid, _⟩ :=
      published_slice_pair_saturation_existsUnique lowerSlice upperSlice
        ha hu hak huk hlower.nonempty hupper.nonempty hsum hactive htotal
        hlowerOuter hupperOuter
    cases branch with
    | lower =>
        obtain ⟨slice, hpivots⟩ :=
          exists_publishedLowerPivotSlice_of_saturated_predecessors
            lowerSlice hvalid hdeep hlower.nonempty hupper.nonempty hlower
            (fun u' hu' ↦ hpredecessors a u'
              (Nat.add_lt_add_left hu' a))
            hnoCap hnoCup hnoStrong
        apply Or.inl
        refine ⟨hvalid, slice, ?_, hpivots⟩
        rw [slice.index_eq, lowerSlice.index_eq]
    | upper =>
        obtain ⟨slice, hpivots⟩ :=
          exists_publishedUpperPivotSlice_of_saturated_predecessors
            upperSlice hvalid hdeep hlower.nonempty hupper.nonempty hupper
            (fun a' ha' ↦ hpredecessors a' u
              (Nat.add_lt_add_right ha' u))
            hnoCap hnoCup hnoStrong
        apply Or.inr
        refine ⟨hvalid, slice, ?_, hpivots⟩
        rw [slice.index_eq, upperSlice.index_eq]
  exact context.false_of_visibleCoreBound_and_residualStrictness
    hselected (hvisible context) (hstrict context)

end ErdosSzekeres

end
