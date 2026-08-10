module

public import ErdosSzekeres.PrimeTwoDeletionCounterexample
public import ErdosSzekeres.DecompositionPrimeNormalization

@[expose] public section

/-!
# A realizable target-free mutation into the decomposable class

Moving one point in the seven-point prime-deletion counterexample flips
exactly triple `(0,5,6)`. The resulting swept coloring remains strong-six-free
and is represented by an explicit decomposition tree. This is a positive
control for mutation normalization, not a general normalization theorem.
-/

namespace ErdosSzekeres
namespace PrimeMutationPositiveControl

def tree : RankProfileCollision.DecompositionTree 7 :=
  .node
    (.node (.leaf 0) (.node (.leaf 3) (.leaf 4)))
    (.node (.leaf 5) (.node (.leaf 2) (.node (.leaf 1) (.leaf 6))))

def color : TripleColoring 7 := tree.coloring

theorem tree_wellFormed :
    RankProfileCollision.DecompositionTree.WellFormed tree := by
  simp [tree, RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem tree_vertices : tree.vertices = Finset.univ := by
  decide

theorem color_decomposable : IsDecomposable color := by
  have h := RankProfileCollision.DecompositionTree.decomposableOn
    tree tree_wellFormed
  rw [tree_vertices] at h
  exact h

noncomputable section

def points : Fin 7 → Point 2 := ![
  ![0, -81],
  ![1, 0],
  ![2, -6],
  ![3, -54],
  ![4, -74],
  ![5, -30],
  ![6, -21]]

set_option maxHeartbeats 4000000 in
noncomputable def configuration : SweptConfiguration 7 where
  point := points
  sweep_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num [points]
  generalPosition := generalPosition_of_ordered points (by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals norm_num at hij
    all_goals norm_num at hjk
    all_goals norm_num [points, orientation])

set_option maxHeartbeats 4000000 in
theorem configuration_coloring : configuration.tripleColoring = color := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [configuration, points,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    orientation]
  all_goals simp [color, tree,
    RankProfileCollision.DecompositionTree.coloring,
    RankProfileCollision.DecompositionTree.vertices]

theorem color_sweepRealizable : IsSweepRealizable color :=
  ⟨configuration, configuration_coloring⟩

set_option maxRecDepth 100000 in
theorem color_noStrongSetBool_six :
    ∀ s : Finset (Fin 7), s.card = 6 →
      RankProfileCollision.strongPolygonSetBool color s = false := by
  decide

theorem color_noStrongSix :
    ¬ContainsStrongPolygonSet color Finset.univ 6 := by
  rintro ⟨polygon, _hsub, hcard, hstrong⟩
  have htrue :=
    (RankProfileCollision.strongPolygonSetBool_eq_true_iff color polygon).2
      hstrong
  rw [color_noStrongSetBool_six polygon hcard] at htrue
  contradiction

def changedTriple : OrderedTriple 7 :=
  ⟨0, 5, 6, by decide, by decide⟩

theorem source_to_color_singleMutation :
    SingleTripleMutation PrimeTwoDeletionCounterexample.color color := by
  refine ⟨changedTriple, by decide, ?_⟩
  rintro ⟨i, j, k, hij, hjk⟩ hne
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals simp_all [changedTriple, OrderedTriple.mk.injEq,
    PrimeTwoDeletionCounterexample.color,
    PrimeTwoDeletionCounterexample.leftCodes, color, tree,
    RankProfileCollision.DecompositionTree.coloring,
    RankProfileCollision.DecompositionTree.vertices]

/-- A kernel-checked realizable, target-free single-triple mutation from the
prime source coloring to a decomposable target coloring. -/
theorem source_to_color_targetFreeMutation :
    TargetFreeRealizableMutationStepAt 6
      PrimeTwoDeletionCounterexample.color color :=
  ⟨PrimeTwoDeletionCounterexample.color_sweepRealizable,
    color_sweepRealizable,
    PrimeTwoDeletionCounterexample.color_noStrongSix,
    color_noStrongSix,
    source_to_color_singleMutation⟩

end

end PrimeMutationPositiveControl
end ErdosSzekeres

end
