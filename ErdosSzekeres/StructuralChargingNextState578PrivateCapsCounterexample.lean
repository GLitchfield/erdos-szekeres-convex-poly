module

public import ErdosSzekeres.StructuralChargingNextState578PrivateCaps
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# Shared-core obstruction for distinct private caps

Six distinct private four-caps need not provide six disjoint resources.  The
recursively decomposable nine-vertex coloring below avoids a five-cap, a
seven-cup, and a strong eight-set while all six caps share the same three
vertices.  This is a kernel-checked obstruction to a packing or bounded
middle-pair-multiplicity inference.  It does not include the terminal-cap or
`32/23` density hypotheses of the live state-578 residual.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578PrivateCapsCounterexample

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def lowerTree : RankProfileCollision.DecompositionTree 9 :=
  .node (.leaf 0)
    (.node (.leaf 3)
      (.node (.leaf 1)
        (.node (.node (.leaf 4) (.leaf 5)) (.leaf 2))))

def upperTree : RankProfileCollision.DecompositionTree 9 :=
  .node (.leaf 6) (.node (.leaf 7) (.leaf 8))

def tree : RankProfileCollision.DecompositionTree 9 :=
  .node lowerTree upperTree

def color : TripleColoring 9 := tree.coloring

def support : Finset (Fin 9) := tree.vertices

def owners : Finset (Fin 9) := {0, 1, 2, 3, 4, 5}

def core : Finset (Fin 9) := {6, 7, 8}

def capFor (x : Fin 9) : Finset (Fin 9) := insert x core

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
  simp [tree, lowerTree, upperTree,
    RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem support_eq_univ : support = Finset.univ := by decide

theorem support_decomposable : IsDecomposableOn color support := by
  exact tree.decomposableOn tree_wellFormed

theorem owners_card : owners.card = 6 := by decide

theorem core_card : core.card = 3 := by decide

theorem owners_core_disjoint : Disjoint owners core := by decide

theorem private_caps (x : Fin 9) (hx : x ∈ owners) :
    capFor x ∈ capWitnesses color support 4 ∧
    owners ∩ capFor x = {x} ∧
    core ⊆ capFor x := by
  have hcapCard : (capFor x).card = 4 := by
    have hxNotCore : x ∉ core :=
      Finset.disjoint_left.mp owners_core_disjoint hx
    rw [capFor, Finset.card_insert_of_notMem hxNotCore, core_card]
  have hcap : IsCapSet color (capFor x) := by
    simpa [IsCapSet] using
      (turnSetBool_eq_true_iff (capFor x) .right).mp (by
        revert x
        decide)
  refine ⟨mem_capWitnesses.mpr ⟨by
      rw [support_eq_univ]
      exact Finset.subset_univ _, hcapCard, hcap⟩, ?_, ?_⟩
  · ext y
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hyOwners, hyCap⟩
      simp only [capFor, Finset.mem_insert] at hyCap
      rcases hyCap with rfl | hyCore
      · rfl
      · exact False.elim
          (Finset.disjoint_left.mp owners_core_disjoint hyOwners hyCore)
    · rintro rfl
      exact ⟨hx, Finset.mem_insert_self _ core⟩
  · exact Finset.subset_insert x core

theorem private_cap_assignment_injective :
    Set.InjOn capFor (owners : Set (Fin 9)) := by
  intro x hx y hy hxy
  apply Finset.singleton_injective
  calc
    {x} = owners ∩ capFor x := (private_caps x hx).2.1.symm
    _ = owners ∩ capFor y := congrArg (owners ∩ ·) hxy
    _ = {y} := (private_caps y hy).2.1

theorem private_cap_image_card : (owners.image capFor).card = 6 := by
  rw [Finset.card_image_of_injOn private_cap_assignment_injective, owners_card]

theorem no_cap_five_bool :
    ∀ s : Finset (Fin 9), s.card = 5 → turnSetBool s .right = false := by
  decide

theorem no_cup_seven_bool :
    ∀ s : Finset (Fin 9), s.card = 7 → turnSetBool s .left = false := by
  decide

theorem no_strong_eight_bool :
    ∀ s : Finset (Fin 9), s.card = 8 →
      RankProfileCollision.strongPolygonSetBool color s = false := by
  decide

theorem no_cap_five : ¬ContainsCapSet color support 5 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cap_five_bool witness hcard
  have htrue : turnSetBool witness .right = true :=
    (turnSetBool_eq_true_iff witness .right).mpr (by
      simpa [IsCapSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_cup_seven : ¬ContainsCupSet color support 7 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cup_seven_bool witness hcard
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

/-- A target-free recursively decomposable coloring can have six distinct
four-caps with private owners and one common three-vertex core. -/
theorem six_distinct_privateCaps_can_share_three_vertex_core :
    IsDecomposableOn color support ∧
    ¬ContainsCapSet color support 5 ∧
    ¬ContainsCupSet color support 7 ∧
    ¬ContainsStrongPolygonSet color support 8 ∧
    owners.card = 6 ∧ core.card = 3 ∧
    (∀ x ∈ owners,
      capFor x ∈ capWitnesses color support 4 ∧
      owners ∩ capFor x = {x} ∧ core ⊆ capFor x) ∧
    Set.InjOn capFor (owners : Set (Fin 9)) ∧
    (owners.image capFor).card = 6 := by
  exact ⟨support_decomposable, no_cap_five, no_cup_seven, no_strong_eight,
    owners_card, core_card, private_caps, private_cap_assignment_injective,
    private_cap_image_card⟩

end StructuralChargingNextState578PrivateCapsCounterexample
end ErdosSzekeres

end
