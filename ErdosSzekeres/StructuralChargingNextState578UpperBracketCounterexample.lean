module

public import ErdosSzekeres.StructuralChargingNextState578UpperBracket
public import ErdosSzekeres.RankProfileCollision
public import ErdosSzekeres.DecomposableRealization

@[expose] public section

/-!
# Two cap columns do not force an upper bracket

This nine-vertex recursively decomposable coloring has two disjoint lower
four-caps.  Every source vertex in either cap owns a four-cup meeting that cap
only at the source, every pair has the same root first-joint split, and every
cup has exactly one upper sweep endpoint.  The coloring avoids a five-cup,
seven-cap, and strong eight-set, so no argument using only two cap columns and
the local endpoint law can force a two-upper-endpoint bracket.

The example does not have six cap blocks or the exact 32/23 density.  Those
global hypotheses remain the only possible repair of the bracket route.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578UpperBracketCounterexample

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

def pair27 : RankProfileCollision.DecompositionTree 9 :=
  .node (.leaf 2) (.leaf 7)

def branch527 : RankProfileCollision.DecompositionTree 9 :=
  .node (.leaf 5) pair27

def branch8527 : RankProfileCollision.DecompositionTree 9 :=
  .node (.leaf 8) branch527

def pair14 : RankProfileCollision.DecompositionTree 9 :=
  .node (.leaf 1) (.leaf 4)

def branch148527 : RankProfileCollision.DecompositionTree 9 :=
  .node pair14 branch8527

def branch6148527 : RankProfileCollision.DecompositionTree 9 :=
  .node (.leaf 6) branch148527

def lowerTree : RankProfileCollision.DecompositionTree 9 :=
  .node (.leaf 3) branch6148527

def upperTree : RankProfileCollision.DecompositionTree 9 :=
  .leaf 0

def tree : RankProfileCollision.DecompositionTree 9 :=
  .node lowerTree upperTree

def color : TripleColoring 9 := tree.coloring

def lower : Finset (Fin 9) := lowerTree.vertices

def upper : Finset (Fin 9) := upperTree.vertices

def support : Finset (Fin 9) := lower ∪ upper

def capA : Finset (Fin 9) := {1, 2, 7, 8}

def capB : Finset (Fin 9) := {3, 4, 5, 6}

def capAt (j : Fin 2) : Finset (Fin 9) :=
  ![capA, capB] j

def sourceAt (j : Fin 2) (c : Fin 4) : Fin 9 :=
  ![![1, 2, 7, 8], ![3, 4, 5, 6]] j c

def rowAt (j : Fin 2) (c : Fin 4) : Finset (Fin 9) :=
  ![![{0, 1, 3, 4}, {0, 2, 3, 4}, {0, 4, 6, 7}, {0, 4, 6, 8}],
    ![{0, 1, 3, 7}, {0, 1, 4, 7}, {0, 2, 5, 7}, {0, 1, 6, 7}]] j c

/-- Nine vertices are necessary for two disjoint four-sets in one child and a
nonempty opposite child.  Thus the example below is cardinality-minimal for
this local obstruction. -/
theorem nine_le_card_of_two_disjoint_four_sets_and_extra
    {n : ℕ} {a b lower upper : Finset (Fin n)}
    (ha : a.card = 4) (hb : b.card = 4) (hab : Disjoint a b)
    (haLower : a ⊆ lower) (hbLower : b ⊆ lower)
    (hupper : upper.Nonempty) (hlowerUpper : Disjoint lower upper) :
    9 ≤ (lower ∪ upper).card := by
  have habCard : (a ∪ b).card = 8 := by
    rw [Finset.card_union_of_disjoint hab, ha, hb]
  have habSub : a ∪ b ⊆ lower := Finset.union_subset haLower hbLower
  have hlowerCard : 8 ≤ lower.card := by
    rw [← habCard]
    exact Finset.card_le_card habSub
  have hupperCard : 1 ≤ upper.card := Finset.card_pos.mpr hupper
  rw [Finset.card_union_of_disjoint hlowerUpper]
  omega

/-- Executable monochromaticity check for the concrete coloring. -/
def turnSetBool (s : Finset (Fin 9)) (turn : Turn) : Bool :=
  (List.finRange 9).all fun i ↦
    (List.finRange 9).all fun j ↦
      (List.finRange 9).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              decide (color ⟨i, j, k, hij, hjk⟩ = turn)
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 9)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 9, t.i ∈ s → t.j ∈ s → t.k ∈ s →
        color t = turn := by
  constructor
  · intro h t hi hj hk
    have hiCheck := (List.all_eq_true.mp h) t.i (List.mem_finRange t.i)
    have hjCheck := (List.all_eq_true.mp hiCheck) t.j (List.mem_finRange t.j)
    have hkCheck := (List.all_eq_true.mp hjCheck) t.k (List.mem_finRange t.k)
    simpa [turnSetBool, t.hij, t.hjk, hi, hj, hk] using hkCheck
  · intro h
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    apply List.all_eq_true.mpr
    intro k _
    by_cases hij : i < j
    · by_cases hjk : j < k
      · by_cases hi : i ∈ s
        · by_cases hj : j ∈ s
          · by_cases hk : k ∈ s
            · simp [hij, hjk, hi, hj, hk,
                h ⟨i, j, k, hij, hjk⟩ hi hj hk]
            · simp [hij, hjk, hi, hj, hk]
          · simp [hij, hjk, hi, hj]
        · simp [hij, hjk, hi]
      · simp [hij, hjk]
    · simp [hij]

theorem tree_wellFormed : tree.WellFormed := by
  simp [tree, lowerTree, upperTree, branch6148527, branch148527,
    pair14, branch8527, branch527, pair27,
    RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem support_eq_univ : support = Finset.univ := by decide

theorem root_deep : HasDeepBelowSplit color lower upper := by
  exact RankProfileCollision.DecompositionTree.node_split lowerTree upperTree
    (by decide)

theorem support_decomposable : IsDecomposableOn color support := by
  simpa [color, support, lower, upper, tree,
    RankProfileCollision.DecompositionTree.vertices] using
    tree.decomposableOn tree_wellFormed

theorem color_decomposable : IsDecomposable color := by
  simpa [IsDecomposable, support_eq_univ] using support_decomposable

theorem color_sweepRealizable : IsSweepRealizable color :=
  color_decomposable.isSweepRealizable

theorem capAt_turn_right (j : Fin 2) :
    turnSetBool (capAt j) .right = true := by
  fin_cases j <;> decide

theorem capAt_mem (j : Fin 2) :
    capAt j ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by fin_cases j <;> decide, by fin_cases j <;> decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff (capAt j) .right).mp (capAt_turn_right j)

theorem capAt_subset_lower (j : Fin 2) : capAt j ⊆ lower := by
  fin_cases j <;> decide

theorem capAt_disjoint : Disjoint (capAt 0) (capAt 1) := by decide

theorem sourceAt_mem (j : Fin 2) (c : Fin 4) : sourceAt j c ∈ capAt j := by
  fin_cases j <;> fin_cases c <;> decide

theorem rowAt_turn_left (j : Fin 2) (c : Fin 4) :
    turnSetBool (rowAt j c) .left = true := by
  fin_cases j <;> fin_cases c <;> decide

theorem rowAt_mem (j : Fin 2) (c : Fin 4) :
    rowAt j c ∈ capWitnesses color.dual support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by fin_cases j <;> fin_cases c <;> decide,
    by fin_cases j <;> fin_cases c <;> decide, ?_⟩
  apply isCapSet_dual_iff.mpr
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff (rowAt j c) .left).mp (rowAt_turn_left j c)

theorem rowAt_inter_capAt (j : Fin 2) (c : Fin 4) :
    rowAt j c ∩ capAt j = {sourceAt j c} := by
  fin_cases j <;> fin_cases c <;> decide

theorem rowAt_oneUpper (j : Fin 2) (c : Fin 4) :
    CupFourOneUpperEndpointShape578 (rowAt j c) lower upper := by
  have hcupNode :
      rowAt j c ∈ capWitnesses color.dual (lower ∪ upper) 4 := by
    simpa [support] using rowAt_mem j c
  have hnotUpper : ¬rowAt j c ⊆ upper := by
    fin_cases j <;> fin_cases c <;> decide
  have hnotLower : ¬rowAt j c ⊆ lower := by
    fin_cases j <;> fin_cases c <;> decide
  have hshape : CupFourLowerEndpointShape578 (rowAt j c) lower upper :=
    ⟨(mem_capWitnesses.mp hcupNode).2.1,
      cupFour_deepSplit_upper_subset_endpoints root_deep hcupNode hnotUpper⟩
  exact hshape.oneUpper_of_upper_card_le_one
    (mem_capWitnesses.mp hcupNode).1 hnotLower (by decide)

theorem rootLower_decomposable : IsDecomposableOn color lower := by
  exact support_decomposable.subset (by simp [support]) (by decide)

noncomputable def rootLowerTree : DecompositionTree color lower :=
  Classical.choice
    (DecompositionTree.exists_of_isDecomposableOn rootLower_decomposable)

def rootUpperTree : DecompositionTree color upper := by
  simpa [upper, upperTree,
    RankProfileCollision.DecompositionTree.vertices] using
    (DecompositionTree.singleton (χ := color) (0 : Fin 9))

noncomputable def decompTree : DecompositionTree color support := by
  simpa [support] using
    (DecompositionTree.split rootLowerTree rootUpperTree root_deep)

def rootNode : DecompositionSplit color :=
  ⟨lower, upper, root_deep⟩

theorem root_lookup : decompTree.splitAtPath [] = some rootNode := by
  simp [decompTree, rootNode, DecompositionTree.splitAtPath]

theorem rowAt_has_root_firstJoint (j : Fin 2) (c : Fin 4) :
    ∃ joint : CupCapFirstJointSplit578 decompTree (rowAt j c) (capAt j),
      joint.path = [] ∧ joint.node = rootNode := by
  fin_cases j <;> fin_cases c <;>
    refine ⟨{
      path := []
      node := rootNode
      lookup := root_lookup
      allocated := DecompositionTree.IsLowestSeparatingPath.root
        (by decide) (by decide) (by decide)
      union_local := by decide
      not_all_lower := by decide
      not_all_upper := by decide
    }, rfl, rfl⟩

theorem no_seven_lower_upperBracket :
    ¬∃ left right,
      left ∈ upper ∧ right ∈ upper ∧ left < right ∧
        7 ≤ (lowerBracket578 lower left right).card := by
  decide

theorem no_cap_seven_bool :
    ∀ s : Finset (Fin 9), s.card = 7 → turnSetBool s .right = false := by
  decide

theorem no_cup_five_bool :
    ∀ s : Finset (Fin 9), s.card = 5 → turnSetBool s .left = false := by
  decide

theorem no_strong_eight_bool :
    ∀ s : Finset (Fin 9), s.card = 8 →
      RankProfileCollision.strongPolygonSetBool color s = false := by
  decide

theorem no_cap_seven : ¬ContainsCapSet color support 7 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cap_seven_bool witness hcard
  have htrue : turnSetBool witness .right = true :=
    (turnSetBool_eq_true_iff witness .right).mpr (by
      simpa [IsCapSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_cup_five : ¬ContainsCupSet color support 5 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cup_five_bool witness hcard
  have htrue : turnSetBool witness .left = true :=
    (turnSetBool_eq_true_iff witness .left).mpr (by
      simpa [IsCupSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_strong_eight : ¬ContainsStrongPolygonSet color support 8 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_strong_eight_bool witness hcard
  have htrue :=
    (RankProfileCollision.strongPolygonSetBool_eq_true_iff color witness).2
      hwitness
  rw [hfalse] at htrue
  contradiction

/-- Kernel-checked obstruction to any local two-column proof of the collective
upper-bracket target. -/
theorem two_columns_with_only_oneUpper_rows_are_target_free :
    IsDecomposable color ∧
    IsSweepRealizable color ∧
    HasDeepBelowSplit color lower upper ∧
    Disjoint (capAt 0) (capAt 1) ∧
    (∀ j, capAt j ∈ capWitnesses color support 4 ∧ capAt j ⊆ lower) ∧
    (∀ j c,
      sourceAt j c ∈ capAt j ∧
      rowAt j c ∈ capWitnesses color.dual support 4 ∧
      rowAt j c ∩ capAt j = {sourceAt j c} ∧
      CupFourOneUpperEndpointShape578 (rowAt j c) lower upper ∧
      ∃ joint : CupCapFirstJointSplit578 decompTree (rowAt j c) (capAt j),
        joint.path = [] ∧ joint.node = rootNode) ∧
    (¬∃ left right,
      left ∈ upper ∧ right ∈ upper ∧ left < right ∧
        7 ≤ (lowerBracket578 lower left right).card) ∧
    ¬ContainsCupSet color support 5 ∧
    ¬ContainsCapSet color support 7 ∧
    ¬ContainsStrongPolygonSet color support 8 := by
  exact ⟨color_decomposable, color_sweepRealizable, root_deep,
    capAt_disjoint, fun j ↦ ⟨capAt_mem j, capAt_subset_lower j⟩,
    fun j c ↦ ⟨sourceAt_mem j c, rowAt_mem j c,
      rowAt_inter_capAt j c, rowAt_oneUpper j c,
      rowAt_has_root_firstJoint j c⟩,
    no_seven_lower_upperBracket, no_cup_five, no_cap_seven,
    no_strong_eight⟩

end StructuralChargingNextState578UpperBracketCounterexample
end ErdosSzekeres

end
