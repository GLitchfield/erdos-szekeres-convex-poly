module

public import ErdosSzekeres.StructuralChargingSelectedBranchPivot

@[expose] public section

/-!
# Counterexample to all-node entering-pivot injectivity

Local entering pivots are injective at one fixed split. They are not injective
across nested split data on pivot value alone: a root hidden gap and a hidden
gap in its upper support can have the same canonical pivot. This file does not
construct a coloring or an explicit `DecompositionTree` realizing both splits.
-/

namespace ErdosSzekeres
namespace StructuralChargingTreePivotCounterexample

def rootLower : Finset (Fin 5) := {1, 3}

def rootUpper : Finset (Fin 5) := {0, 2, 4}

def descendantLower : Finset (Fin 5) := {0, 4}

def descendantUpper : Finset (Fin 5) := {2}

theorem root_children_disjoint : Disjoint rootLower rootUpper := by decide

theorem descendant_children_disjoint :
    Disjoint descendantLower descendantUpper := by
  decide

theorem descendant_support_eq_root_upper :
    descendantLower ∪ descendantUpper = rootUpper := by
  decide

def rootHiddenLowerSpan : SweepSpanEndpoints 5 := ⟨1, 3⟩

theorem rootHiddenLowerSpan_isHidden :
    IsHiddenLowerGap rootLower rootUpper rootHiddenLowerSpan := by
  constructor
  · classical
    norm_num [rootHiddenLowerSpan, SweepSpanEndpoints.IsAdjacentIn, rootLower]
    all_goals decide
  · exact ⟨2, by decide, by decide, by decide⟩

def rootHiddenLowerSource : HiddenGapSource rootLower rootUpper .right :=
  ⟨rootHiddenLowerSpan,
    mem_hiddenGapSources_iff.mpr rootHiddenLowerSpan_isHidden⟩

def descendantHiddenLowerSpan : SweepSpanEndpoints 5 := ⟨0, 4⟩

theorem descendantHiddenLowerSpan_isHidden :
    IsHiddenLowerGap descendantLower descendantUpper descendantHiddenLowerSpan := by
  constructor
  · classical
    norm_num [descendantHiddenLowerSpan, SweepSpanEndpoints.IsAdjacentIn,
      descendantLower]
    all_goals decide
  · exact ⟨2, by decide, by decide, by decide⟩

def descendantHiddenLowerSource :
    HiddenGapSource descendantLower descendantUpper .right :=
  ⟨descendantHiddenLowerSpan,
    mem_hiddenGapSources_iff.mpr descendantHiddenLowerSpan_isHidden⟩

theorem root_enteringPivot_eq_two :
    rootHiddenLowerSource.enteringPivot = 2 := by
  apply Fin.ext
  have hbetween := rootHiddenLowerSource.enteringPivot_between
  norm_num [rootHiddenLowerSource, rootHiddenLowerSpan] at hbetween ⊢
  omega

theorem descendant_enteringPivot_eq_two :
    descendantHiddenLowerSource.enteringPivot = 2 := by
  have hmem := descendantHiddenLowerSource.enteringPivot_mem_oppositeChild
    descendant_children_disjoint
  simpa [descendantUpper] using hmem

/-- The two nested set-level occurrences receive distinct candidate address
labels, but their canonical entering pivots coincide. -/
theorem ancestor_descendant_enteringPivot_collision :
    rootHiddenLowerSource.enteringPivot =
        descendantHiddenLowerSource.enteringPivot ∧
      ([] : List Bool) ≠ [true] := by
  constructor
  · rw [root_enteringPivot_eq_two, descendant_enteringPivot_eq_two]
  · decide

/-- Consequently, canonical pivot value alone cannot inject these nested
hidden-gap data when compared using the candidate address labels. -/
theorem not_all_nested_enteringPivots_distinct :
    ¬(rootHiddenLowerSource.enteringPivot =
        descendantHiddenLowerSource.enteringPivot →
      ([] : List Bool) = [true]) := by
  intro h
  exact ancestor_descendant_enteringPivot_collision.2
    (h ancestor_descendant_enteringPivot_collision.1)

end StructuralChargingTreePivotCounterexample
end ErdosSzekeres

end
