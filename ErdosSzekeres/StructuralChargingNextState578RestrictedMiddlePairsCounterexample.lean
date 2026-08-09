module

public import ErdosSzekeres.StructuralChargingNextState578RestrictedMiddlePairs
public import ErdosSzekeres.RankProfileCollision
public import ErdosSzekeres.DecomposableRealization

@[expose] public section

/-!
# Two disjoint lower middle pairs do not force a state-578 target

This cardinality-minimal ten-vertex recursively decomposable coloring has a
lower four-cap and two cap-disjoint four-cups.  The cups share exactly their
two upper endpoints and have disjoint sweep-middle pairs in the lower child,
but the coloring contains no five-cup, seven-cap, or strong eight-set.

The example expires the first local consumer of the density-extracted middle
pairs.  It does not have the exact 32-vertex density or six lower cap blocks.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578RestrictedMiddlePairsCounterexample

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

def pair83 : RankProfileCollision.DecompositionTree 10 :=
  .node (.leaf 8) (.leaf 3)

def pair75 : RankProfileCollision.DecompositionTree 10 :=
  .node (.leaf 7) (.leaf 5)

def triple756 : RankProfileCollision.DecompositionTree 10 :=
  .node pair75 (.leaf 6)

def block : RankProfileCollision.DecompositionTree 10 :=
  .node pair83 triple756

def block0 : RankProfileCollision.DecompositionTree 10 :=
  .node block (.leaf 0)

def pair21 : RankProfileCollision.DecompositionTree 10 :=
  .node (.leaf 2) (.leaf 1)

def lowerTree : RankProfileCollision.DecompositionTree 10 :=
  .node block0 pair21

def upperTree : RankProfileCollision.DecompositionTree 10 :=
  .node (.leaf 4) (.leaf 9)

def tree : RankProfileCollision.DecompositionTree 10 :=
  .node lowerTree upperTree

def color : TripleColoring 10 := tree.coloring

def lower : Finset (Fin 10) := lowerTree.vertices

def upper : Finset (Fin 10) := upperTree.vertices

def support : Finset (Fin 10) := lower ∪ upper

def cap : Finset (Fin 10) := {0, 1, 2, 3}

def cupA : Finset (Fin 10) := {4, 5, 6, 9}

def cupB : Finset (Fin 10) := {4, 7, 8, 9}

/-- Executable monochromaticity check for the concrete coloring. -/
def turnSetBool (s : Finset (Fin 10)) (turn : Turn) : Bool :=
  (List.finRange 10).all fun i ↦
    (List.finRange 10).all fun j ↦
      (List.finRange 10).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              decide (color ⟨i, j, k, hij, hjk⟩ = turn)
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 10)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 10, t.i ∈ s → t.j ∈ s → t.k ∈ s →
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
  simp [tree, lowerTree, upperTree, block0, block, triple756,
    pair83, pair75, pair21,
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

theorem cap_mem : cap ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff cap .right).mp (by decide)

theorem cupA_mem : cupA ∈ capWitnesses color.dual support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  apply isCapSet_dual_iff.mpr
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff cupA .left).mp (by decide)

theorem cupB_mem : cupB ∈ capWitnesses color.dual support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  apply isCapSet_dual_iff.mpr
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff cupB .left).mp (by decide)

theorem cupA_inter_cupB : cupA ∩ cupB = {4, 9} := by decide

theorem cupA_cap_disjoint : Disjoint cupA cap := by decide

theorem cupB_cap_disjoint : Disjoint cupB cap := by decide

theorem cap_subset_lower : cap ⊆ lower := by decide

theorem cupA_not_subset_upper : ¬cupA ⊆ upper := by decide

theorem cupB_not_subset_upper : ¬cupB ⊆ upper := by decide

theorem cupA_sort : cupA.sort (fun a b => a ≤ b) = [4, 5, 6, 9] := by
  simpa [cupA] using
    (List.toFinset_sort (r := fun a b : Fin 10 => a ≤ b)
      (l := [4, 5, 6, 9]) (by decide)).2 (by decide)

theorem cupB_sort : cupB.sort (fun a b => a ≤ b) = [4, 7, 8, 9] := by
  simpa [cupB] using
    (List.toFinset_sort (r := fun a b : Fin 10 => a ≤ b)
      (l := [4, 7, 8, 9]) (by decide)).2 (by decide)

theorem cupA_order_one :
    cupA.orderEmbOfFin (by decide) (1 : Fin 4) = 5 := by
  rw [Finset.orderEmbOfFin_apply]
  simp only [cupA_sort]
  rfl

theorem cupA_order_two :
    cupA.orderEmbOfFin (by decide) (2 : Fin 4) = 6 := by
  rw [Finset.orderEmbOfFin_apply]
  simp only [cupA_sort]
  rfl

theorem cupB_order_one :
    cupB.orderEmbOfFin (by decide) (1 : Fin 4) = 7 := by
  rw [Finset.orderEmbOfFin_apply]
  simp only [cupB_sort]
  rfl

theorem cupB_order_two :
    cupB.orderEmbOfFin (by decide) (2 : Fin 4) = 8 := by
  rw [Finset.orderEmbOfFin_apply]
  simp only [cupB_sort]
  rfl

theorem cupA_middlePair :
    sweepMiddlePair578 cupA (by decide) = {5, 6} := by
  simp [sweepMiddlePair578, cupA_order_one, cupA_order_two]

theorem cupB_middlePair :
    sweepMiddlePair578 cupB (by decide) = {7, 8} := by
  simp [sweepMiddlePair578, cupB_order_one, cupB_order_two]

theorem middlePairs_disjoint :
    Disjoint (sweepMiddlePair578 cupA (by decide))
      (sweepMiddlePair578 cupB (by decide)) := by
  rw [cupA_middlePair, cupB_middlePair]
  decide

theorem middlePairs_subset_lower :
    sweepMiddlePair578 cupA (by decide) ∪
      sweepMiddlePair578 cupB (by decide) ⊆ lower := by
  rw [cupA_middlePair, cupB_middlePair]
  decide

theorem no_cap_seven_bool :
    ∀ s : Finset (Fin 10), s.card = 7 → turnSetBool s .right = false := by
  decide

theorem no_cup_five_bool :
    ∀ s : Finset (Fin 10), s.card = 5 → turnSetBool s .left = false := by
  decide

theorem no_strong_eight_bool :
    ∀ s : Finset (Fin 10), s.card = 8 →
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

/-- Kernel-checked minimum obstruction to consuming two disjoint lower
sweep-middle pairs by a local target argument. -/
theorem two_disjoint_lower_middlePairs_are_target_free :
    IsDecomposable color ∧
    IsSweepRealizable color ∧
    HasDeepBelowSplit color lower upper ∧
    cap ∈ capWitnesses color support 4 ∧
    cupA ∈ capWitnesses color.dual support 4 ∧
    cupB ∈ capWitnesses color.dual support 4 ∧
    cap ⊆ lower ∧
    Disjoint cupA cap ∧ Disjoint cupB cap ∧
    cupA ∩ cupB = {4, 9} ∧
    ¬cupA ⊆ upper ∧ ¬cupB ⊆ upper ∧
    sweepMiddlePair578 cupA (by decide) = {5, 6} ∧
    sweepMiddlePair578 cupB (by decide) = {7, 8} ∧
    Disjoint (sweepMiddlePair578 cupA (by decide))
      (sweepMiddlePair578 cupB (by decide)) ∧
    sweepMiddlePair578 cupA (by decide) ∪
      sweepMiddlePair578 cupB (by decide) ⊆ lower ∧
    ¬ContainsCupSet color support 5 ∧
    ¬ContainsCapSet color support 7 ∧
    ¬ContainsStrongPolygonSet color support 8 := by
  exact ⟨color_decomposable, color_sweepRealizable, root_deep, cap_mem,
    cupA_mem, cupB_mem, cap_subset_lower, cupA_cap_disjoint,
    cupB_cap_disjoint, cupA_inter_cupB, cupA_not_subset_upper,
    cupB_not_subset_upper, cupA_middlePair, cupB_middlePair,
    middlePairs_disjoint, middlePairs_subset_lower, no_cup_five,
    no_cap_seven, no_strong_eight⟩

end StructuralChargingNextState578RestrictedMiddlePairsCounterexample
end ErdosSzekeres

end
