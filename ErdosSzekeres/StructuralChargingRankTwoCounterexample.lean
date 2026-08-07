module

public import ErdosSzekeres.StructuralChargingSpanFrontier
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# A rank-two counterexample to per-frontier Pascal allocation

The exact-rank-two frontier is the sequence of adjacent child changes.  An
alternating seven-vertex split therefore has six retained spans, while the
rank-two layer of the proposed `k = 7` Pascal allocation has only five slots.
This file kernel-checks that obstruction in an open recursively decomposable
context; it is not merely a replay of the bounded Python census.  It also
rules out the first proposed repair: summing locally adjacent rank-two spans
over a decomposition tree need not be bounded by the number of globally
adjacent pairs.
-/

namespace ErdosSzekeres
namespace StructuralChargingRankTwoCounterexample

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def lowerTree : RankProfileCollision.DecompositionTree 7 :=
  .node (.leaf 0) (.node (.leaf 4) (.node (.leaf 2) (.leaf 6)))

def upperTree : RankProfileCollision.DecompositionTree 7 :=
  .node (.leaf 1) (.node (.leaf 3) (.leaf 5))

def tree : RankProfileCollision.DecompositionTree 7 := .node lowerTree upperTree

def color : TripleColoring 7 :=
  RankProfileCollision.DecompositionTree.coloring tree

def lower : Finset (Fin 7) :=
  RankProfileCollision.DecompositionTree.vertices lowerTree

def upper : Finset (Fin 7) :=
  RankProfileCollision.DecompositionTree.vertices upperTree

def support : Finset (Fin 7) := lower ∪ upper

theorem root_deep : HasDeepBelowSplit color lower upper := by
  exact RankProfileCollision.DecompositionTree.node_split
    lowerTree upperTree (by decide)

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

theorem no_strong_seven_bool :
    ∀ polygon : Finset (Fin 7), polygon.card = 7 →
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

def alternatingSpans : Finset (SweepSpanEndpoints 7) :=
  {⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 6⟩}

theorem alternatingSpans_subset_frontier :
    alternatingSpans ⊆
      allocatedExactRankFrontier color lower upper .right 2 := by
  intro span hspan
  simp only [alternatingSpans, Finset.mem_insert, Finset.mem_singleton] at hspan
  rcases hspan with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [mem_allocatedExactRankFrontier_two_iff_adjacent_crossing root_deep] <;>
    constructor
  all_goals norm_num [SweepSpanEndpoints.CrossesSplit, lower, upper, lowerTree,
    upperTree, RankProfileCollision.DecompositionTree.vertices]
  all_goals decide

/-- The proposed individual-span capacity inequality is false already at
rank two in an open decomposable `k = 7` context. -/
theorem rank_two_frontier_exceeds_pascal_demand :
    publishedSpanPascalDemand 7 2 <
      (allocatedExactRankFrontier color lower upper .right 2).card := by
  have hcard := Finset.card_le_card alternatingSpans_subset_frontier
  have halt : alternatingSpans.card = 6 := by decide
  rw [halt] at hcard
  norm_num [publishedSpanPascalDemand]
  omega

/-- Equivalently, no injection of these individual rank-two spans into the
five proposed Pascal slots can exist. -/
theorem no_rank_two_slotting :
    IsEmpty (AllocatedExactRankSlotting color lower upper .right 2 7) := by
  constructor
  intro slotting
  have hle :=
    allocatedExactRankFrontier_card_le_spanPascalDemand_of_slotting slotting
  exact (not_lt_of_ge hle) rank_two_frontier_exceeds_pascal_demand

end StructuralChargingRankTwoCounterexample

namespace StructuralChargingRankTwoGlobalCountCounterexample

/-! The root of this tree separates `{0, 2}` from `{1}`.  Consequently
`(0, 2)` is adjacent in the lower child even though `1` lies globally between
its endpoints. -/

def childLowerTree : RankProfileCollision.DecompositionTree 3 := .leaf 0

def childUpperTree : RankProfileCollision.DecompositionTree 3 := .leaf 2

def lowerTree : RankProfileCollision.DecompositionTree 3 :=
  .node childLowerTree childUpperTree

def upperTree : RankProfileCollision.DecompositionTree 3 := .leaf 1

def tree : RankProfileCollision.DecompositionTree 3 := .node lowerTree upperTree

def color : TripleColoring 3 := tree.coloring

def childLower : Finset (Fin 3) := childLowerTree.vertices

def childUpper : Finset (Fin 3) := childUpperTree.vertices

def lower : Finset (Fin 3) := lowerTree.vertices

def upper : Finset (Fin 3) := upperTree.vertices

def support : Finset (Fin 3) := lower ∪ upper

theorem child_deep : HasDeepBelowSplit color childLower childUpper := by
  constructor
  · decide
  · intro t hi hj hk _ _
    have hsub : ({t.i, t.j, t.k} : Finset (Fin 3)) ⊆
        childLower ∪ childUpper := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    have hcard := Finset.card_le_card hsub
    have hijk : t.i ≠ t.k := ne_of_lt (t.hij.trans t.hjk)
    have htripleCard : ({t.i, t.j, t.k} : Finset (Fin 3)).card = 3 := by
      simp [t.hij.ne, t.hjk.ne, hijk]
    have hpairCard : (childLower ∪ childUpper).card = 2 := by decide
    rw [htripleCard, hpairCard] at hcard
    omega

theorem root_deep : HasDeepBelowSplit color lower upper := by
  exact RankProfileCollision.DecompositionTree.node_split
    lowerTree upperTree (by decide)

def childSpans : Finset (SweepSpanEndpoints 3) := {⟨0, 2⟩}

def rootSpans : Finset (SweepSpanEndpoints 3) := {⟨0, 1⟩, ⟨1, 2⟩}

theorem childSpans_subset_frontier :
    childSpans ⊆
      allocatedExactRankFrontier color childLower childUpper .right 2 := by
  intro span hspan
  simp only [childSpans, Finset.mem_singleton] at hspan
  subst span
  rw [mem_allocatedExactRankFrontier_two_iff_adjacent_crossing child_deep]
  norm_num [SweepSpanEndpoints.CrossesSplit, childLower, childUpper,
    childLowerTree, childUpperTree,
    RankProfileCollision.DecompositionTree.vertices]
  decide

theorem rootSpans_subset_frontier :
    rootSpans ⊆ allocatedExactRankFrontier color lower upper .right 2 := by
  intro span hspan
  simp only [rootSpans, Finset.mem_insert, Finset.mem_singleton] at hspan
  rcases hspan with rfl | rfl <;>
    rw [mem_allocatedExactRankFrontier_two_iff_adjacent_crossing root_deep] <;>
    constructor
  all_goals norm_num [SweepSpanEndpoints.CrossesSplit, lower, upper, lowerTree,
    upperTree, childLowerTree, childUpperTree,
    RankProfileCollision.DecompositionTree.vertices]
  all_goals decide

/-- Local adjacency is not global adjacency: the two root spans and the one
lower-child span already exceed the two global adjacency gaps. -/
theorem two_node_rank_two_mass_exceeds_global_adjacent_count :
    support.card - 1 <
      (allocatedExactRankFrontier color childLower childUpper .right 2).card +
        (allocatedExactRankFrontier color lower upper .right 2).card := by
  have hchild := Finset.card_le_card childSpans_subset_frontier
  have hroot := Finset.card_le_card rootSpans_subset_frontier
  have hchildCard : childSpans.card = 1 := by decide
  have hrootCard : rootSpans.card = 2 := by decide
  have hsupportCard : support.card = 3 := by decide
  omega

end StructuralChargingRankTwoGlobalCountCounterexample
end ErdosSzekeres

end
