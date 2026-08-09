module

public import ErdosSzekeres.StructuralChargingNextState578DeletionLedger
public import ErdosSzekeres.RankProfileCollision
public import ErdosSzekeres.DecomposableRealization

@[expose] public section

/-!
# A target-free four-cap deletion star at one first joint split

This exact eight-vertex recursively decomposable coloring has a four-cap and,
for each of its vertices, a four-cup meeting the cap only at that vertex.  The
four cups share a three-vertex core.  All four cup/cap pairs have the root as
their first joint split and all four cups have the lower-endpoint shape there.

Thus the color-sensitive one-column conclusion of the deletion ledger is
sharp: even target avoidance, recursive decomposability, a common first joint
split, and four synchronized endpoint shapes do not by themselves close state
`(5,7,8)`.  The example does not have the exact 32-vertex density or the other
five saturated cap blocks.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578DeletionEndpointCounterexample

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

def pair72 : RankProfileCollision.DecompositionTree 8 :=
  .node (.leaf 7) (.leaf 2)

def pair63 : RankProfileCollision.DecompositionTree 8 :=
  .node (.leaf 6) (.leaf 3)

def pair54 : RankProfileCollision.DecompositionTree 8 :=
  .node (.leaf 5) (.leaf 4)

def middle : RankProfileCollision.DecompositionTree 8 :=
  .node pair63 pair54

def block : RankProfileCollision.DecompositionTree 8 :=
  .node pair72 middle

def lowerRankTree : RankProfileCollision.DecompositionTree 8 :=
  .node block (.leaf 1)

def rankTree : RankProfileCollision.DecompositionTree 8 :=
  .node lowerRankTree (.leaf 0)

def color : TripleColoring 8 := rankTree.coloring

def rootLower : Finset (Fin 8) := lowerRankTree.vertices

def rootUpper : Finset (Fin 8) := {0}

def support : Finset (Fin 8) := rootLower ∪ rootUpper

def cap : Finset (Fin 8) := {2, 3, 4, 5}

def commonCore : Finset (Fin 8) := {0, 1, 6}

def spoke (c : Fin 8) : Finset (Fin 8) := insert c commonCore

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

theorem rankTree_wellFormed : rankTree.WellFormed := by
  simp [rankTree, lowerRankTree, block, middle, pair72, pair63, pair54,
    RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem support_eq_univ : support = Finset.univ := by decide

theorem support_eq_rankVertices : support = rankTree.vertices := by decide

theorem root_deep : HasDeepBelowSplit color rootLower rootUpper := by
  simpa [color, rootLower, rootUpper] using
    (RankProfileCollision.DecompositionTree.node_split
      lowerRankTree (.leaf 0) (by decide))

theorem support_decomposable : IsDecomposableOn color support := by
  rw [support_eq_rankVertices]
  exact rankTree.decomposableOn rankTree_wellFormed

theorem color_decomposable : IsDecomposable color := by
  simpa [IsDecomposable, support_eq_univ] using support_decomposable

theorem color_sweepRealizable : IsSweepRealizable color :=
  color_decomposable.isSweepRealizable

theorem cap_mem : cap ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff cap .right).mp (by decide)

theorem spoke_mem (c : Fin 8) (hc : c ∈ cap) :
    spoke c ∈ capWitnesses color.dual support 4 := by
  simp only [cap, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    apply mem_capWitnesses.mpr <;>
    refine ⟨by decide, by decide, ?_⟩ <;>
    apply isCapSet_dual_iff.mpr <;>
    simpa [IsCupSet] using
      (turnSetBool_eq_true_iff _ .left).mp (by decide)

theorem spoke_inter_cap (c : Fin 8) (hc : c ∈ cap) :
    spoke c ∩ cap = {c} := by
  simp only [cap, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem spoke_erase_source (c : Fin 8) (hc : c ∈ cap) :
    (spoke c).erase c = commonCore := by
  simp only [cap, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem commonCore_card : commonCore.card = 3 := by decide

theorem spoke_lowerEndpointShape (c : Fin 8) (hc : c ∈ cap) :
    CupFourLowerEndpointShape578 (spoke c) rootLower rootUpper := by
  have hcup := spoke_mem c hc
  have hcupNode :
      spoke c ∈ capWitnesses color.dual (rootLower ∪ rootUpper) 4 := by
    simpa [support] using hcup
  have hnotUpper : ¬spoke c ⊆ rootUpper := by
    intro hsub
    have hone : (1 : Fin 8) ∈ rootUpper := hsub (by
      simp [spoke, commonCore])
    simp [rootUpper] at hone
  exact ⟨(mem_capWitnesses.mp hcup).2.1,
    cupFour_deepSplit_upper_subset_endpoints root_deep hcupNode hnotUpper⟩

theorem rootLower_decomposable : IsDecomposableOn color rootLower := by
  exact support_decomposable.subset (by simp [support]) (by decide)

noncomputable def rootLowerTree : DecompositionTree color rootLower :=
  Classical.choice
    (DecompositionTree.exists_of_isDecomposableOn rootLower_decomposable)

def rootUpperTree : DecompositionTree color rootUpper := by
  simpa [rootUpper] using
    (DecompositionTree.singleton (χ := color) (0 : Fin 8))

noncomputable def decompTree : DecompositionTree color support := by
  simpa [support] using
    (DecompositionTree.split rootLowerTree rootUpperTree root_deep)

def rootNode : DecompositionSplit color :=
  ⟨rootLower, rootUpper, root_deep⟩

theorem root_lookup : decompTree.splitAtPath [] = some rootNode := by
  simp [decompTree, rootNode, DecompositionTree.splitAtPath]

/-- All four cup/cap pairs really do have the same root first-joint address;
the common address is not merely a relaxed label. -/
theorem spoke_has_root_firstJoint (c : Fin 8) (hc : c ∈ cap) :
    ∃ joint : CupCapFirstJointSplit578 decompTree (spoke c) cap,
      joint.path = [] ∧ joint.node = rootNode := by
  simp only [cap, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
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

/-- Kernel-checked obstruction to closing the all-rows endpoint branch one
cap column at a time. -/
theorem deletion_endpoint_star_is_target_free :
    IsDecomposable color ∧
    IsSweepRealizable color ∧
    cap ∈ capWitnesses color support 4 ∧
    commonCore.card = 3 ∧
    (∀ c ∈ cap,
      spoke c ∈ capWitnesses color.dual support 4 ∧
      spoke c ∩ cap = {c} ∧
      (spoke c).erase c = commonCore ∧
      CupFourLowerEndpointShape578 (spoke c) rootLower rootUpper ∧
      ∃ joint : CupCapFirstJointSplit578 decompTree (spoke c) cap,
        joint.path = [] ∧ joint.node = rootNode) ∧
    ¬ContainsCupSet color support 5 ∧
    ¬ContainsCapSet color support 7 ∧
    ¬ContainsStrongPolygonSet color support 8 := by
  exact ⟨color_decomposable, color_sweepRealizable, cap_mem,
    commonCore_card, fun c hc ↦
      ⟨spoke_mem c hc, spoke_inter_cap c hc, spoke_erase_source c hc,
        spoke_lowerEndpointShape c hc, spoke_has_root_firstJoint c hc⟩,
    no_cup_five, no_cap_seven, no_strong_eight⟩

end StructuralChargingNextState578DeletionEndpointCounterexample
end ErdosSzekeres

end
