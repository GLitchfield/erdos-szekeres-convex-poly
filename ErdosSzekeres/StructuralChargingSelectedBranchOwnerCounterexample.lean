module

public import ErdosSzekeres.StructuralChargingConservedBranch
public import ErdosSzekeres.StructuralChargingGapTokenConservation

@[expose] public section

/-!
# Counterexample to unqualified selected-branch owner membership

The first feasible nonsingleton published boundary has child sizes `2+10`
and unique saturated upper branch.  A lower hidden gap can nevertheless be
owned by a lower-child vertex.  Thus a conserved hidden-gap owner does not, in
general, lie in the uniquely saturated child.

This refutes only the unqualified branch-membership bridge.  A future theorem
may use a color- or obligation-specific witness seed different from the gap's
right-endpoint owner.
-/

namespace ErdosSzekeres
namespace StructuralChargingSelectedBranchOwnerCounterexample

def lower : Finset (Fin 12) := {0, 11}

def upper : Finset (Fin 12) := Finset.univ \ lower

theorem lower_nonempty : lower.Nonempty := by decide

theorem upper_nonempty : upper.Nonempty := by decide

theorem children_disjoint : Disjoint lower upper := by decide

theorem lower_card : lower.card = 2 := by decide

theorem upper_card : upper.card = 10 := by decide

noncomputable def lowerSlice : PublishedChildSlice 4 6 6 lower :=
  Classical.choice (exists_publishedChildSlice (by omega) lower_nonempty)

noncomputable def upperSlice : PublishedCapChildSlice 4 6 6 upper :=
  Classical.choose (exists_publishedCapChildSlice_core_superset
    (seed := ∅) (by omega) upper_nonempty (by simp) (by simp))

theorem publishedChildIndex_eq_two :
    publishedChildIndex 4 6 6 2 = 2 := by
  rw [publishedChildIndex, Nat.findGreatest_eq_iff]
  refine ⟨by omega, ?_, ?_⟩
  · intro _
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
  · intro index htwo hsix
    interval_cases index <;>
      norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
        Finset.sum_Icc_succ_top]

theorem lowerSlice_index : lowerSlice.index = 2 := by
  rw [lowerSlice.index_eq, lower_card]
  exact publishedChildIndex_eq_two

theorem upperSlice_index : upperSlice.index = 3 := by
  rw [upperSlice.index_eq, upper_card]
  exact publishedCapChildIndex_eq_three_at_first_saturated_boundary
    (by omega) (by omega)

/-- The actual slice pair instantiates the first nonsingleton published
boundary and has a unique saturated branch. -/
theorem slice_pair_saturation_existsUnique :
    ∃! branch : PublishedSaturatedBranch,
      branch.Valid 4 6 6 upperSlice.index lowerSlice.index := by
  exact published_slice_pair_saturation_existsUnique
    lowerSlice upperSlice (by omega) (by omega) (by omega) (by omega)
    lower_nonempty upper_nonempty
    (by simp [lowerSlice_index, upperSlice_index])
    (by omega)
    (by norm_num [lower_card, upper_card, decomposableThreshold,
      decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top])
    (by norm_num [lower_card, decomposableThreshold,
      decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top])
    (by norm_num [upper_card, decomposableThreshold,
      decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top])

/-- Concretely, the unique saturated branch is the upper child. -/
theorem valid_branch_eq_upper {branch : PublishedSaturatedBranch}
    (hvalid : branch.Valid 4 6 6 upperSlice.index lowerSlice.index) :
    branch = .upper := by
  cases branch with
  | lower =>
      simp [PublishedSaturatedBranch.Valid, lowerSlice_index] at hvalid
  | upper => rfl

theorem upper_branch_valid :
    PublishedSaturatedBranch.Valid 4 6 6
      upperSlice.index lowerSlice.index .upper := by
  simp [PublishedSaturatedBranch.Valid, lowerSlice_index, upperSlice_index]

def hiddenLowerSpan : SweepSpanEndpoints 12 := ⟨0, 11⟩

theorem hiddenLowerSpan_isHidden :
    IsHiddenLowerGap lower upper hiddenLowerSpan := by
  constructor
  · classical
    norm_num [hiddenLowerSpan, SweepSpanEndpoints.IsAdjacentIn, lower]
    all_goals decide
  · refine ⟨1, ?_, by decide, by decide⟩
    decide

def hiddenLowerSource : HiddenGapSource lower upper .right :=
  ⟨hiddenLowerSpan, mem_hiddenGapSources_iff.mpr hiddenLowerSpan_isHidden⟩

/-- The conserved right-endpoint owner belongs to the lower child, not the
unique saturated upper child. -/
theorem hiddenLowerSource_owner_not_in_saturated_child :
    hiddenLowerSource.1.right ∉
      PublishedSaturatedBranch.child lower upper .upper := by
  decide

/-- The counterexample packages uniqueness and owner failure in one exact
statement. -/
theorem unique_saturated_branch_misses_hidden_owner :
    PublishedSaturatedBranch.Valid 4 6 6
        upperSlice.index lowerSlice.index .upper ∧
      (∀ branch : PublishedSaturatedBranch,
        PublishedSaturatedBranch.Valid 4 6 6
          upperSlice.index lowerSlice.index branch → branch = .upper) ∧
      hiddenLowerSource.1.right ∉
        PublishedSaturatedBranch.child lower upper .upper := by
  exact ⟨upper_branch_valid, fun _ ↦ valid_branch_eq_upper,
    hiddenLowerSource_owner_not_in_saturated_child⟩

/-- Therefore unique arithmetic saturation does not imply that every hidden
gap's conserved owner follows the saturated branch. -/
theorem not_all_hidden_owners_follow_saturated_branch :
    ¬∀ source : HiddenGapSource lower upper .right,
      source.1.right ∈
        PublishedSaturatedBranch.child lower upper .upper := by
  intro hall
  exact hiddenLowerSource_owner_not_in_saturated_child
    (hall hiddenLowerSource)

end StructuralChargingSelectedBranchOwnerCounterexample
end ErdosSzekeres

end
