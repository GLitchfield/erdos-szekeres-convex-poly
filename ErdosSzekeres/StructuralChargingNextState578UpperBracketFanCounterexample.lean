module

public import ErdosSzekeres.StructuralChargingNextState578UpperBracketCounterexample

@[expose] public section

/-!
# A nine-source fan does not close the bracket route locally

This exact 13-vertex recursively decomposable coloring has three disjoint
lower four-caps and twelve source-indexed deletion cups. Nine cap sources lie
below the unique upper vertex, and every associated row has exactly one upper
sweep endpoint. Nevertheless the coloring has no five-cup, seven-cap, or
strong eight-set.

Thus the compiled nine-source exterior-fan reduction is useful
infrastructure, but its next consumer must use the remaining six-column or
32/23-density data essentially. A three-column fan alone cannot close the
state-578 branch.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578UpperBracketFanCounterexample

set_option maxHeartbeats 24000000
set_option maxRecDepth 100000

def pair11_2 : RankProfileCollision.DecompositionTree 13 :=
  .node (.leaf 11) (.leaf 2)

def pair6_0 : RankProfileCollision.DecompositionTree 13 :=
  .node (.leaf 6) (.leaf 0)

def branch8_60 : RankProfileCollision.DecompositionTree 13 :=
  .node (.leaf 8) pair6_0

def pair7_3 : RankProfileCollision.DecompositionTree 13 :=
  .node (.leaf 7) (.leaf 3)

def branch12_73 : RankProfileCollision.DecompositionTree 13 :=
  .node (.leaf 12) pair7_3

def branch12_73_4 : RankProfileCollision.DecompositionTree 13 :=
  .node branch12_73 (.leaf 4)

def pair10_1 : RankProfileCollision.DecompositionTree 13 :=
  .node (.leaf 10) (.leaf 1)

def branch12_73_4_10_1 : RankProfileCollision.DecompositionTree 13 :=
  .node branch12_73_4 pair10_1

def branch5 : RankProfileCollision.DecompositionTree 13 :=
  .node (.leaf 5) branch12_73_4_10_1

def lowerRight : RankProfileCollision.DecompositionTree 13 :=
  .node branch8_60 branch5

def lowerTree : RankProfileCollision.DecompositionTree 13 :=
  .node pair11_2 lowerRight

def upperTree : RankProfileCollision.DecompositionTree 13 :=
  .leaf 9

def tree : RankProfileCollision.DecompositionTree 13 :=
  .node lowerTree upperTree

def color : TripleColoring 13 := tree.coloring

def lower : Finset (Fin 13) := lowerTree.vertices

def upper : Finset (Fin 13) := upperTree.vertices

def support : Finset (Fin 13) := lower ∪ upper

def capA : Finset (Fin 13) := {0, 3, 4, 12}

def capB : Finset (Fin 13) := {1, 5, 8, 11}

def capC : Finset (Fin 13) := {2, 6, 7, 10}

def capAt (j : Fin 3) : Finset (Fin 13) :=
  ![capA, capB, capC] j

def sourceAt (j : Fin 3) (c : Fin 4) : Fin 13 :=
  ![![0, 3, 4, 12], ![1, 5, 8, 11], ![2, 6, 7, 10]] j c

def rowAt (j : Fin 3) (c : Fin 4) : Finset (Fin 13) :=
  ![![{0, 2, 5, 9}, {1, 2, 3, 9}, {1, 2, 4, 9}, {9, 10, 11, 12}],
    ![{1, 2, 3, 9}, {0, 2, 5, 9}, {0, 2, 8, 9}, {9, 10, 11, 12}],
    ![{0, 2, 3, 9}, {1, 6, 8, 9}, {1, 3, 7, 9}, {9, 10, 11, 12}]] j c

def fanSources : Finset (Fin 13) := {0, 1, 2, 3, 4, 5, 6, 7, 8}

/-- Executable monochromaticity check for the concrete coloring. -/
def turnSetBool (s : Finset (Fin 13)) (turn : Turn) : Bool :=
  (List.finRange 13).all fun i ↦
    (List.finRange 13).all fun j ↦
      (List.finRange 13).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              decide (color ⟨i, j, k, hij, hjk⟩ = turn)
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 13)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 13, t.i ∈ s → t.j ∈ s → t.k ∈ s →
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
  simp [tree, lowerTree, upperTree, lowerRight, pair11_2, branch8_60,
    pair6_0, branch5, branch12_73_4_10_1, branch12_73_4, branch12_73,
    pair7_3, pair10_1, RankProfileCollision.DecompositionTree.WellFormed,
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

theorem capAt_turn_right (j : Fin 3) :
    turnSetBool (capAt j) .right = true := by
  fin_cases j <;> decide

theorem capAt_mem (j : Fin 3) :
    capAt j ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by fin_cases j <;> decide, by fin_cases j <;> decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff (capAt j) .right).mp (capAt_turn_right j)

theorem capAt_subset_lower (j : Fin 3) : capAt j ⊆ lower := by
  fin_cases j <;> decide

theorem capAt_pairwise :
    ([capAt 0, capAt 1, capAt 2] : List (Finset (Fin 13))).Pairwise Disjoint := by
  decide

theorem sourceAt_mem (j : Fin 3) (c : Fin 4) : sourceAt j c ∈ capAt j := by
  fin_cases j <;> fin_cases c <;> decide

theorem rowAt_turn_left (j : Fin 3) (c : Fin 4) :
    turnSetBool (rowAt j c) .left = true := by
  fin_cases j <;> fin_cases c <;> decide

theorem rowAt_mem (j : Fin 3) (c : Fin 4) :
    rowAt j c ∈ capWitnesses color.dual support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by fin_cases j <;> fin_cases c <;> decide,
    by fin_cases j <;> fin_cases c <;> decide, ?_⟩
  apply isCapSet_dual_iff.mpr
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff (rowAt j c) .left).mp (rowAt_turn_left j c)

theorem rowAt_inter_capAt (j : Fin 3) (c : Fin 4) :
    rowAt j c ∩ capAt j = {sourceAt j c} := by
  fin_cases j <;> fin_cases c <;> decide

theorem rowAt_oneUpper (j : Fin 3) (c : Fin 4) :
    CupFourOneUpperEndpointShape578 (rowAt j c) lower upper := by
  have hcupNode : rowAt j c ∈ capWitnesses color.dual (lower ∪ upper) 4 := by
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

theorem fanSources_card : fanSources.card = 9 := by decide

theorem fanSources_below_upper : ∀ x ∈ fanSources, x < (9 : Fin 13) := by
  decide

theorem fanSources_subset_capUnion :
    fanSources ⊆ capAt 0 ∪ capAt 1 ∪ capAt 2 := by
  decide

theorem rootLower_decomposable : IsDecomposableOn color lower := by
  exact support_decomposable.subset (by simp [support]) (by decide)

noncomputable def rootLowerTree : DecompositionTree color lower :=
  Classical.choice
    (DecompositionTree.exists_of_isDecomposableOn rootLower_decomposable)

def rootUpperTree : DecompositionTree color upper := by
  simpa [upper, upperTree,
    RankProfileCollision.DecompositionTree.vertices] using
    (DecompositionTree.singleton (χ := color) (9 : Fin 13))

noncomputable def decompTree : DecompositionTree color support := by
  simpa [support] using
    (DecompositionTree.split rootLowerTree rootUpperTree root_deep)

def rootNode : DecompositionSplit color :=
  ⟨lower, upper, root_deep⟩

theorem root_lookup : decompTree.splitAtPath [] = some rootNode := by
  simp [decompTree, rootNode, DecompositionTree.splitAtPath]

theorem rowAt_has_root_firstJoint (j : Fin 3) (c : Fin 4) :
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

theorem sort_mem_sublistsLen_finRange (s : Finset (Fin 13)) (k : ℕ)
    (hcard : s.card = k) :
    s.sort (· ≤ ·) ∈ List.sublistsLen k (List.finRange 13) := by
  rw [List.mem_sublistsLen]
  constructor
  · rw [← Fin.sort_univ 13]
    apply List.sublist_of_subperm_of_pairwise
      ((Finset.sort_nodup s _).subperm ?_)
      (Finset.pairwise_sort s _) (Finset.pairwise_sort Finset.univ _)
    intro x hx
    simp only [Finset.mem_sort] at hx ⊢
    exact Finset.mem_univ x
  · simpa [Finset.length_sort] using hcard

def noCupFiveCheck : Bool :=
  (List.sublistsLen 5 (List.finRange 13)).all fun s ↦
    !(turnSetBool s.toFinset .left)

theorem noCupFiveCheck_eq_true : noCupFiveCheck = true := by
  decide

def noCapSevenCheck : Bool :=
  (List.sublistsLen 7 (List.finRange 13)).all fun s ↦
    !(turnSetBool s.toFinset .right)

theorem noCapSevenCheck_eq_true : noCapSevenCheck = true := by
  decide

def noStrongEightCheck : Bool :=
  (List.sublistsLen 8 (List.finRange 13)).all fun s ↦
    !(RankProfileCollision.strongPolygonSetBool color s.toFinset)

theorem noStrongEightCheck_eq_true : noStrongEightCheck = true := by
  decide

theorem no_cap_seven_bool :
    ∀ s : Finset (Fin 13), s.card = 7 → turnSetBool s .right = false := by
  intro s hcard
  have hcheck :
      (List.sublistsLen 7 (List.finRange 13)).all (fun row ↦
        !(turnSetBool row.toFinset .right)) = true := by
    simpa [noCapSevenCheck] using noCapSevenCheck_eq_true
  have hrow := (List.all_eq_true.mp hcheck) (s.sort (· ≤ ·))
    (sort_mem_sublistsLen_finRange s 7 hcard)
  simpa using hrow

theorem no_cup_five_bool :
    ∀ s : Finset (Fin 13), s.card = 5 → turnSetBool s .left = false := by
  intro s hcard
  have hcheck :
      (List.sublistsLen 5 (List.finRange 13)).all (fun row ↦
        !(turnSetBool row.toFinset .left)) = true := by
    simpa [noCupFiveCheck] using noCupFiveCheck_eq_true
  have hrow := (List.all_eq_true.mp hcheck) (s.sort (· ≤ ·))
    (sort_mem_sublistsLen_finRange s 5 hcard)
  simpa using hrow

theorem no_strong_eight_bool :
    ∀ s : Finset (Fin 13), s.card = 8 →
      RankProfileCollision.strongPolygonSetBool color s = false := by
  intro s hcard
  have hcheck :
      (List.sublistsLen 8 (List.finRange 13)).all (fun row ↦
        !(RankProfileCollision.strongPolygonSetBool color row.toFinset)) = true := by
    simpa [noStrongEightCheck] using noStrongEightCheck_eq_true
  have hrow := (List.all_eq_true.mp hcheck) (s.sort (· ≤ ·))
    (sort_mem_sublistsLen_finRange s 8 hcard)
  simpa using hrow

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

/-- Kernel-checked three-column obstruction to consuming the nine-source fan
without additional six-column or density information. -/
theorem three_columns_realize_nine_source_fan_and_avoid_targets :
    IsDecomposable color ∧
    IsSweepRealizable color ∧
    HasDeepBelowSplit color lower upper ∧
    ([capAt 0, capAt 1, capAt 2] : List (Finset (Fin 13))).Pairwise Disjoint ∧
    (∀ j, capAt j ∈ capWitnesses color support 4 ∧ capAt j ⊆ lower) ∧
    (∀ j c,
      sourceAt j c ∈ capAt j ∧
      rowAt j c ∈ capWitnesses color.dual support 4 ∧
      rowAt j c ∩ capAt j = {sourceAt j c} ∧
      CupFourOneUpperEndpointShape578 (rowAt j c) lower upper ∧
      ∃ joint : CupCapFirstJointSplit578 decompTree (rowAt j c) (capAt j),
        joint.path = [] ∧ joint.node = rootNode) ∧
    fanSources.card = 9 ∧
    (∀ x ∈ fanSources, x < (9 : Fin 13)) ∧
    fanSources ⊆ capAt 0 ∪ capAt 1 ∪ capAt 2 ∧
    (¬∃ left right,
      left ∈ upper ∧ right ∈ upper ∧ left < right ∧
        7 ≤ (lowerBracket578 lower left right).card) ∧
    ¬ContainsCupSet color support 5 ∧
    ¬ContainsCapSet color support 7 ∧
    ¬ContainsStrongPolygonSet color support 8 := by
  exact ⟨color_decomposable, color_sweepRealizable, root_deep,
    capAt_pairwise, fun j ↦ ⟨capAt_mem j, capAt_subset_lower j⟩,
    fun j c ↦ ⟨sourceAt_mem j c, rowAt_mem j c,
      rowAt_inter_capAt j c, rowAt_oneUpper j c,
      rowAt_has_root_firstJoint j c⟩,
    fanSources_card, fanSources_below_upper, fanSources_subset_capUnion,
    no_seven_lower_upperBracket, no_cup_five, no_cap_seven,
    no_strong_eight⟩

end StructuralChargingNextState578UpperBracketFanCounterexample
end ErdosSzekeres

end
