module

public import ErdosSzekeres.StructuralChargingGapTokenConservation
public import ErdosSzekeres.StructuralChargingRankTwoCounterexample
public import ErdosSzekeres.StructuralChargingCrossColorReuseCounterexample

@[expose] public section

/-!
# Regression gates for conserved sweep-gap tokens

The general owner equivalence is instantiated on the two frozen obstructions
that any tree-global charge must survive.  On the three-point tree, the child
gap is transported to a root gap rather than counted again.  On the ten-point
root, the two five-vertex token families merge to exactly ten parent tokens;
no cap/cup common-span quotient or false single-coefficient payment is used.
-/

namespace ErdosSzekeres
namespace StructuralChargingGapTokenRegression

namespace ThreePoint

open StructuralChargingRankTwoGlobalCountCounterexample

theorem lower_nonempty : lower.Nonempty := by decide

theorem upper_nonempty : upper.Nonempty := by decide

theorem children_disjoint : Disjoint lower upper := by decide

theorem support_nonempty : support.Nonempty := by decide

def lowerGapZeroTwo : SweepGapToken lower :=
  .inl ⟨⟨0, 2⟩, by
    classical
    norm_num [SweepSpanEndpoints.IsAdjacentIn, lower, lowerTree,
      childLowerTree, childUpperTree,
      RankProfileCollision.DecompositionTree.vertices]
    all_goals decide⟩

def lowerSentinel : SweepGapToken lower := .inr ()

def upperSentinel : SweepGapToken upper := .inr ()

def rootGapZeroOne : SweepGapToken support :=
  .inl ⟨⟨0, 1⟩, by
    classical
    norm_num [SweepSpanEndpoints.IsAdjacentIn, support, lower, upper,
      lowerTree, upperTree, childLowerTree, childUpperTree,
      RankProfileCollision.DecompositionTree.vertices]
    all_goals decide⟩

def rootGapOneTwo : SweepGapToken support :=
  .inl ⟨⟨1, 2⟩, by
    classical
    norm_num [SweepSpanEndpoints.IsAdjacentIn, support, lower, upper,
      lowerTree, upperTree, childLowerTree, childUpperTree,
      RankProfileCollision.DecompositionTree.vertices]
    all_goals decide⟩

def rootSentinel : SweepGapToken support := .inr ()

/-- The apparent extra child gap `(0,2)` is the same owner thread as the
parent gap `(1,2)`. -/
theorem lowerGapZeroTwo_transports_to_rootGapOneTwo :
    sweepGapTokenMergeEquiv lower_nonempty upper_nonempty children_disjoint
        (.inl lowerGapZeroTwo) =
      rootGapOneTwo := by
  apply SweepGapToken.owner_injective
    (lower_nonempty.mono Finset.subset_union_left)
  rw [sweepGapTokenMergeEquiv_owner]
  rfl

/-- The lower-child sentinel remains the global sentinel. -/
theorem lowerSentinel_transports_to_rootSentinel :
    sweepGapTokenMergeEquiv lower_nonempty upper_nonempty children_disjoint
        (.inl lowerSentinel) =
      rootSentinel := by
  apply SweepGapToken.owner_injective
    (lower_nonempty.mono Finset.subset_union_left)
  rw [sweepGapTokenMergeEquiv_owner]
  apply Subtype.ext
  decide

/-- The other child sentinel becomes the newly created initial root gap. -/
theorem upperSentinel_transports_to_rootGapZeroOne :
    sweepGapTokenMergeEquiv lower_nonempty upper_nonempty children_disjoint
        (.inr upperSentinel) =
      rootGapZeroOne := by
  apply SweepGapToken.owner_injective
    (lower_nonempty.mono Finset.subset_union_left)
  rw [sweepGapTokenMergeEquiv_owner]
  apply Subtype.ext
  decide

/-- Thus the frozen three-point tree has three conserved tokens on both sides
of its root merge, rather than three local gaps plus two global gaps. -/
theorem root_merge_has_three_tokens :
    Fintype.card (SweepGapToken lower) +
        Fintype.card (SweepGapToken upper) = 3 ∧
      Fintype.card (SweepGapToken support) = 3 := by
  rw [sweepGapToken_card lower_nonempty,
    sweepGapToken_card upper_nonempty,
    sweepGapToken_card support_nonempty]
  decide

end ThreePoint

namespace TenPoint

open StructuralChargingAdjustedCounterexample

theorem lower_nonempty : lower.Nonempty := by decide

theorem upper_nonempty : upper.Nonempty := by decide

theorem children_disjoint : Disjoint lower upper := by decide

theorem support_nonempty : support.Nonempty := by decide

/-- The alternating ten-point root has five child-owned tokens on each side
and exactly ten parent-owned tokens.  This conservation statement does not
identify cap and cup obligations that merely share endpoints. -/
theorem root_merge_has_ten_tokens :
    Fintype.card (SweepGapToken lower) = 5 ∧
      Fintype.card (SweepGapToken upper) = 5 ∧
      Fintype.card (SweepGapToken support) = 10 := by
  rw [sweepGapToken_card lower_nonempty,
    sweepGapToken_card upper_nonempty,
    sweepGapToken_card support_nonempty]
  decide

end TenPoint

end StructuralChargingGapTokenRegression
end ErdosSzekeres

end
