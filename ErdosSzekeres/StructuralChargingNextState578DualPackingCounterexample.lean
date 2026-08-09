module

public import ErdosSzekeres.StructuralChargingNextState578DualPacking
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# Reverse-oriented cup/cap separation is target-free

At a deep split, a lower cup and upper cap form a strong polygon.  The reverse
orientation need not: the recursively decomposable eight-vertex coloring in
this file has a four-cap in the lower child and a disjoint four-cup in the
upper child, while avoiding a seven-cap, a five-cup, and a strong eight-set.

This refutes pair-address equality or reverse separation as a standalone
consumer.  The example does not have the 32-vertex density or singleton-root
hypotheses of the live gate.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578DualPackingCounterexample

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def lowerTree : RankProfileCollision.DecompositionTree 8 :=
  .node (.node (.leaf 0) (.leaf 3)) (.node (.leaf 1) (.leaf 2))

def upperTree : RankProfileCollision.DecompositionTree 8 :=
  .node (.node (.leaf 5) (.leaf 6)) (.node (.leaf 4) (.leaf 7))

def tree : RankProfileCollision.DecompositionTree 8 :=
  .node lowerTree upperTree

def color : TripleColoring 8 := tree.coloring

def cap : Finset (Fin 8) := lowerTree.vertices

def cup : Finset (Fin 8) := upperTree.vertices

def support : Finset (Fin 8) := tree.vertices

/-- Executable monochromaticity check for the concrete coloring. -/
def turnSetBool (s : Finset (Fin 8)) (turn : Turn) : Bool :=
  (List.finRange 8).all fun i ↦
    (List.finRange 8).all fun j ↦
      (List.finRange 8).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              decide (color ⟨i, j, k, hij, hjk⟩ = turn)
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 8)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 8, t.i ∈ s → t.j ∈ s → t.k ∈ s →
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
  simp [tree, lowerTree, upperTree,
    RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem support_eq_univ : support = Finset.univ := by decide

theorem cap_eq : cap = {0, 1, 2, 3} := by decide

theorem cup_eq : cup = {4, 5, 6, 7} := by decide

theorem support_decomposable : IsDecomposableOn color support :=
  tree.decomposableOn tree_wellFormed

theorem root_deep : HasDeepBelowSplit color cap cup := by
  exact RankProfileCollision.DecompositionTree.node_split lowerTree upperTree
    (by decide)

theorem cap_isCapSet : IsCapSet color cap := by
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff cap .right).mp (by decide)

theorem cup_isCupSet : IsCupSet color cup := by
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff cup .left).mp (by decide)

theorem cap_card : cap.card = 4 := by decide

theorem cup_card : cup.card = 4 := by decide

theorem cap_cup_disjoint : Disjoint cap cup := by decide

theorem no_cap_seven_bool :
    ∀ s : Finset (Fin 8), s.card = 7 → turnSetBool s .right = false := by
  decide

theorem no_cup_five_bool :
    ∀ s : Finset (Fin 8), s.card = 5 → turnSetBool s .left = false := by
  decide

theorem no_strong_eight_bool :
    ∀ s : Finset (Fin 8), s.card = 8 →
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

/-- A reverse-oriented separated four-cap/four-cup pair can be recursively
decomposable and avoid all three swapped `(7,5,8)` targets. -/
theorem reverseSeparated_cupCapFour_pair_is_target_free :
    IsDecomposableOn color support ∧
    HasDeepBelowSplit color cap cup ∧
    cap.card = 4 ∧ IsCapSet color cap ∧
    cup.card = 4 ∧ IsCupSet color cup ∧
    Disjoint cap cup ∧
    ¬ContainsCapSet color support 7 ∧
    ¬ContainsCupSet color support 5 ∧
    ¬ContainsStrongPolygonSet color support 8 := by
  exact ⟨support_decomposable, root_deep, cap_card, cap_isCapSet,
    cup_card, cup_isCupSet, cap_cup_disjoint, no_cap_seven,
    no_cup_five, no_strong_eight⟩

end StructuralChargingNextState578DualPackingCounterexample
end ErdosSzekeres

end
