module

public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-! # Fixed decomposable coloring for the endpoint-transition collision -/

namespace ErdosSzekeres
namespace StructuralChargingTransitionHallCollisionData

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def lowerTree : RankProfileCollision.DecompositionTree 12 :=
  .node
    (.node (.leaf 8) (.node (.leaf 2) (.leaf 1)))
    (.node (.node (.leaf 4) (.leaf 7)) (.leaf 10))

def upperTree : RankProfileCollision.DecompositionTree 12 :=
  .node
    (.node (.node (.leaf 0) (.leaf 3))
      (.node (.node (.leaf 6) (.leaf 9)) (.leaf 5)))
    (.leaf 11)

def tree : RankProfileCollision.DecompositionTree 12 := .node lowerTree upperTree

def color : TripleColoring 12 :=
  RankProfileCollision.DecompositionTree.coloring tree

def lower : Finset (Fin 12) :=
  RankProfileCollision.DecompositionTree.vertices lowerTree

def upper : Finset (Fin 12) :=
  RankProfileCollision.DecompositionTree.vertices upperTree

def support : Finset (Fin 12) := lower ∪ upper

theorem support_eq_univ : support = Finset.univ := by decide

theorem tree_wellFormed :
    RankProfileCollision.DecompositionTree.WellFormed tree := by
  simp [tree, lowerTree, upperTree,
    RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem decomposable_support : IsDecomposableOn color support := by
  have h := RankProfileCollision.DecompositionTree.decomposableOn
    tree tree_wellFormed
  simpa [color, support, lower, upper, tree,
    RankProfileCollision.DecompositionTree.vertices] using h

theorem decomposable_lower : IsDecomposableOn color lower := by
  apply decomposable_support.subset Finset.subset_union_left
  decide

theorem decomposable_upper : IsDecomposableOn color upper := by
  apply decomposable_support.subset Finset.subset_union_right
  decide

theorem root_deep : HasDeepBelowSplit color lower upper := by
  exact RankProfileCollision.DecompositionTree.node_split
    lowerTree upperTree (by decide)

theorem no_strong_seven_bool :
    ∀ polygon : Finset (Fin 12), polygon.card = 7 →
      RankProfileCollision.strongPolygonSetBool color polygon = false := by
  decide

theorem no_strong_seven :
    ¬ContainsStrongPolygonSet color support 7 := by
  rintro ⟨polygon, _, hcard, hstrong⟩
  have hfalse := no_strong_seven_bool polygon hcard
  have htrue :=
    (RankProfileCollision.strongPolygonSetBool_eq_true_iff color polygon).2 hstrong
  rw [hfalse] at htrue
  contradiction

end StructuralChargingTransitionHallCollisionData
end ErdosSzekeres

end
