module

public import ErdosSzekeres.StructuralChargingNextState578
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# Counterexample to the first rooted `(5,7,8)` cup-block gate

The centered `5+q+5` gate isolated by the singleton-lower reduction is false,
even for a recursively decomposable coloring. This file kernel-checks the
eleven-vertex counterexample rather than relying on its SAT discovery.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578Counterexample

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def leftTree : RankProfileCollision.DecompositionTree 11 :=
  .node
    (.node
      (.node
        (.node (.leaf 0) (.leaf 1))
        (.leaf 2))
      (.leaf 3))
    (.leaf 4)

def rightTree : RankProfileCollision.DecompositionTree 11 :=
  .node
    (.node
      (.node
        (.node (.leaf 6) (.leaf 7))
        (.leaf 8))
      (.leaf 9))
    (.leaf 10)

def upperTree : RankProfileCollision.DecompositionTree 11 :=
  .node leftTree rightTree

def tree : RankProfileCollision.DecompositionTree 11 :=
  .node (.leaf 5) upperTree

def color : TripleColoring 11 := tree.coloring

def left : Finset (Fin 11) := leftTree.vertices

def right : Finset (Fin 11) := rightTree.vertices

def upper : Finset (Fin 11) := left ∪ right

def support : Finset (Fin 11) := {5} ∪ upper

/-- Executable monochromaticity check for the concrete coloring. -/
def turnSetBool (s : Finset (Fin 11)) (turn : Turn) : Bool :=
  (List.finRange 11).all fun i ↦
    (List.finRange 11).all fun j ↦
      (List.finRange 11).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              decide (color ⟨i, j, k, hij, hjk⟩ = turn)
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 11)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 11, t.i ∈ s → t.j ∈ s → t.k ∈ s → color t = turn := by
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
            · simp [hij, hjk, hi, hj, hk, h ⟨i, j, k, hij, hjk⟩ hi hj hk]
            · simp [hij, hjk, hi, hj, hk]
          · simp [hij, hjk, hi, hj]
        · simp [hij, hjk, hi]
      · simp [hij, hjk]
    · simp [hij]

theorem left_isCupSet : IsCupSet color left := by
  simpa [IsCupSet] using (turnSetBool_eq_true_iff left .left).mp (by decide)

theorem right_isCupSet : IsCupSet color right := by
  simpa [IsCupSet] using (turnSetBool_eq_true_iff right .left).mp (by decide)

theorem upper_decomposable : IsDecomposableOn color upper := by
  have hwell : tree.WellFormed := by
    simp [tree, upperTree, leftTree, rightTree,
      RankProfileCollision.DecompositionTree.WellFormed,
      RankProfileCollision.DecompositionTree.vertices]
  have h := RankProfileCollision.DecompositionTree.decomposableOn tree hwell
  have hvertices : tree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h.subset (by simp) (by decide)

theorem root_deep : HasDeepBelowSplit color {5} upper := by
  have h := RankProfileCollision.DecompositionTree.node_split
    (.leaf (5 : Fin 11)) upperTree (by decide)
  simpa [color, tree, upper, left, right, upperTree, leftTree, rightTree,
    RankProfileCollision.DecompositionTree.vertices] using h

theorem support_eq_univ : support = Finset.univ := by decide

theorem no_cap_five_bool :
    ∀ s : Finset (Fin 11), s.card = 5 → turnSetBool s .right = false := by
  decide

theorem no_cup_seven_bool :
    ∀ s : Finset (Fin 11), s.card = 7 → turnSetBool s .left = false := by
  decide

theorem no_strong_eight_bool :
    ∀ s : Finset (Fin 11), s.card = 8 →
      RankProfileCollision.strongPolygonSetBool color s = false := by
  decide

theorem no_cap_five : ¬ContainsCapSet color support 5 := by
  rintro ⟨cap, _, hcard, hcap⟩
  have hfalse := no_cap_five_bool cap hcard
  have htrue : turnSetBool cap .right = true :=
    (turnSetBool_eq_true_iff cap .right).mpr (by simpa [IsCapSet] using hcap)
  rw [hfalse] at htrue
  contradiction

theorem no_cup_seven : ¬ContainsCupSet color support 7 := by
  rintro ⟨cup, _, hcard, hcup⟩
  have hfalse := no_cup_seven_bool cup hcard
  have htrue : turnSetBool cup .left = true :=
    (turnSetBool_eq_true_iff cup .left).mpr (by simpa [IsCupSet] using hcup)
  rw [hfalse] at htrue
  contradiction

theorem no_strong_eight : ¬ContainsStrongPolygonSet color support 8 := by
  rintro ⟨polygon, _, hcard, hstrong⟩
  have hfalse := no_strong_eight_bool polygon hcard
  have htrue :=
    (RankProfileCollision.strongPolygonSetBool_eq_true_iff color polygon).2 hstrong
  rw [hfalse] at htrue
  contradiction

/-- The proposed rooted `5+q+5` closing gate is false. -/
theorem not_rootedCupBlocks55Force578 : ¬RootedCupBlocks55Force578 := by
  intro hgate
  have hout := hgate (χ := color) (q := 5) (left := left) (right := right)
    (by decide)
    (by decide)
    (by decide)
    (by decide) (by decide) left_isCupSet right_isCupSet
    upper_decomposable.turnSequenceAllowed root_deep
  simpa [support] using hout.elim no_cap_five (fun h ↦ h.elim no_cup_seven no_strong_eight)

end StructuralChargingNextState578Counterexample
end ErdosSzekeres

end
