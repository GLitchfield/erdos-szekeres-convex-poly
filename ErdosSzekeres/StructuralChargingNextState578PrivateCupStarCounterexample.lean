module

public import ErdosSzekeres.StructuralChargingNextState578PrivateCupStar
public import ErdosSzekeres.RankProfileCollision
public import ErdosSzekeres.DecomposableRealization

@[expose] public section

/-!
# A target-free private-cup star with one common tail

This seven-vertex recursively decomposable coloring has a four-cup spine and
four distinct private four-cups, one at each spine vertex.  All four private
cups have exactly the same three-vertex tail.  Thus neither private-cup
injectivity nor decomposability bounds tail reuse.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578PrivateCupStarCounterexample

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

def tree : RankProfileCollision.DecompositionTree 7 :=
  .node
    (.node (.leaf 1) (.leaf 2))
    (.node
      (.node (.leaf 5) (.leaf 4))
      (.node (.leaf 0) (.node (.leaf 3) (.leaf 6))))

/-- Executable tree-support recursion for the concrete certificate. -/
def treeVertices {n : ℕ} : RankProfileCollision.DecompositionTree n →
    Finset (Fin n)
  | .leaf i => {i}
  | .node lower upper => treeVertices lower ∪ treeVertices upper

/-- Executable recursive deep-below coloring for the concrete certificate. -/
def treeColoring {n : ℕ} : RankProfileCollision.DecompositionTree n →
    TripleColoring n
  | .leaf _ => fun _ ↦ .right
  | .node lower upper => fun t ↦
      if t.i ∈ treeVertices lower ∧ t.j ∈ treeVertices lower ∧
          t.k ∈ treeVertices lower then
        treeColoring lower t
      else if t.i ∈ treeVertices upper ∧ t.j ∈ treeVertices upper ∧
          t.k ∈ treeVertices upper then
        treeColoring upper t
      else if t.j ∈ treeVertices lower then .left else .right

theorem treeVertices_eq_vertices {n : ℕ}
    (candidate : RankProfileCollision.DecompositionTree n) :
    treeVertices candidate = candidate.vertices := by
  induction candidate with
  | leaf i => rfl
  | node lower upper ihLower ihUpper =>
      simp only [treeVertices,
        RankProfileCollision.DecompositionTree.vertices, ihLower, ihUpper]

theorem treeColoring_eq_coloring {n : ℕ}
    (candidate : RankProfileCollision.DecompositionTree n) :
    treeColoring candidate = candidate.coloring := by
  induction candidate with
  | leaf i => rfl
  | node lower upper ihLower ihUpper =>
      funext t
      simp only [treeColoring,
        RankProfileCollision.DecompositionTree.coloring,
        treeVertices_eq_vertices, ihLower, ihUpper]

def color : TripleColoring 7 := treeColoring tree

def support : Finset (Fin 7) := treeVertices tree

def spine : Finset (Fin 7) := {3, 4, 5, 6}

def commonTail : Finset (Fin 7) := {0, 1, 2}

def spoke (x : Fin 7) : Finset (Fin 7) := insert x commonTail

/-- Executable equality on turns. -/
def turnEq : Turn → Turn → Bool
  | .left, .left => true
  | .right, .right => true
  | _, _ => false

theorem turnEq_eq_true_iff (first second : Turn) :
    turnEq first second = true ↔ first = second := by
  cases first <;> cases second <;> decide

theorem turnEq_self (turn : Turn) : turnEq turn turn = true := by
  cases turn <;> rfl

/-- Executable monochromaticity checker. -/
def turnSetBool (s : Finset (Fin 7)) (turn : Turn) : Bool :=
  (List.finRange 7).all fun i ↦
    (List.finRange 7).all fun j ↦
      (List.finRange 7).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              turnEq (color ⟨i, j, k, hij, hjk⟩) turn
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 7)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 7, t.i ∈ s → t.j ∈ s → t.k ∈ s →
        color t = turn := by
  constructor
  · intro h t hi hj hk
    have hiCheck := (List.all_eq_true.mp h) t.i (List.mem_finRange t.i)
    have hjCheck := (List.all_eq_true.mp hiCheck) t.j (List.mem_finRange t.j)
    have hkCheck := (List.all_eq_true.mp hjCheck) t.k (List.mem_finRange t.k)
    apply (turnEq_eq_true_iff _ _).mp
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
                h ⟨i, j, k, hij, hjk⟩ hi hj hk, turnEq_self]
            · simp [hij, hjk, hi, hj, hk]
          · simp [hij, hjk, hi, hj]
        · simp [hij, hjk, hi]
      · simp [hij, hjk]
    · simp [hij]

theorem tree_wellFormed : tree.WellFormed := by
  simp [tree, RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem support_eq_univ : support = Finset.univ := by decide

theorem support_decomposable : IsDecomposableOn color support := by
  simpa [color, support, treeVertices_eq_vertices,
    treeColoring_eq_coloring] using tree.decomposableOn tree_wellFormed

theorem color_decomposable : IsDecomposable color := by
  simpa [IsDecomposable, support_eq_univ] using support_decomposable

theorem color_sweepRealizable : IsSweepRealizable color :=
  color_decomposable.isSweepRealizable

theorem spine_mem : spine ∈ capWitnesses color.dual support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  apply isCapSet_dual_iff.mpr
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff spine .left).mp (by decide)

theorem spoke_mem (x : Fin 7) (hx : x ∈ spine) :
    spoke x ∈ capWitnesses color.dual support 4 := by
  simp only [spine, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    apply mem_capWitnesses.mpr <;>
    refine ⟨by decide, by decide, ?_⟩ <;>
    apply isCapSet_dual_iff.mpr <;>
    simpa [IsCupSet] using
      (turnSetBool_eq_true_iff _ .left).mp (by decide)

theorem spoke_inter_spine (x : Fin 7) (hx : x ∈ spine) :
    spoke x ∩ spine = {x} := by
  simp only [spine, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem spoke_erase_owner (x : Fin 7) (hx : x ∈ spine) :
    (spoke x).erase x = commonTail := by
  simp only [spine, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem commonTail_card : commonTail.card = 3 := by decide

theorem no_cup_five_bool :
    ∀ s : Finset (Fin 7), s.card = 5 → turnSetBool s .left = false := by
  decide

theorem no_cap_seven_bool :
    ∀ s : Finset (Fin 7), s.card = 7 → turnSetBool s .right = false := by
  decide

theorem no_cup_five : ¬ContainsCupSet color support 5 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cup_five_bool witness hcard
  have htrue : turnSetBool witness .left = true :=
    (turnSetBool_eq_true_iff witness .left).mpr (by
      simpa [IsCupSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_cap_seven : ¬ContainsCapSet color support 7 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cap_seven_bool witness hcard
  have htrue : turnSetBool witness .right = true :=
    (turnSetBool_eq_true_iff witness .right).mpr (by
      simpa [IsCapSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_strong_eight : ¬ContainsStrongPolygonSet color support 8 := by
  rintro ⟨witness, hwitnessSub, hwitnessCard, _⟩
  have hle := Finset.card_le_card hwitnessSub
  rw [support_eq_univ, Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- A kernel-checked target-free decomposable star in which every private cup
uses the same three exterior vertices. -/
theorem common_tail_privateCupStar_is_target_free :
    IsDecomposable color ∧
    IsSweepRealizable color ∧
    spine ∈ capWitnesses color.dual support 4 ∧
    commonTail.card = 3 ∧
    (∀ x ∈ spine,
      spoke x ∈ capWitnesses color.dual support 4 ∧
      spoke x ∩ spine = {x} ∧
      (spoke x).erase x = commonTail) ∧
    ¬ContainsCupSet color support 5 ∧
    ¬ContainsCapSet color support 7 ∧
    ¬ContainsStrongPolygonSet color support 8 := by
  exact ⟨color_decomposable, color_sweepRealizable, spine_mem,
    commonTail_card, fun x hx ↦
      ⟨spoke_mem x hx, spoke_inter_spine x hx, spoke_erase_owner x hx⟩,
    no_cup_five, no_cap_seven, no_strong_eight⟩

end StructuralChargingNextState578PrivateCupStarCounterexample
end ErdosSzekeres

end
