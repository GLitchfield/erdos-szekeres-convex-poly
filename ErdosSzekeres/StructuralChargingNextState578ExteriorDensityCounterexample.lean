module

public import ErdosSzekeres.StructuralChargingNextState578ExteriorDensity
public import ErdosSzekeres.StructuralChargingNextState578UpperBracketFanCounterexample

@[expose] public section

/-!
# Exact local obstruction after six-column deficit concentration

The six-column count in `StructuralChargingNextState578ExteriorDensity`
produces five source-indexed one-upper rows missing one cap column.  A tempting
next step is to use only that blocker and those five rows to construct a
two-vertex cover of their sweep-middle pairs.  The exact recursively
decomposable 13-vertex coloring below refutes that local step.

The example retains a lower-local four-cap blocker, five distinct exterior
sources, source-private cup rows, one-upper endpoint shapes, genuine root
first-joint allocations with the blocker, and all three target avoidances.
Nevertheless the five sweep-middle pairs have no two-cover.  The model has
only three cap columns and no `32/23` density package, so it does not refute a
future consumer which continues to use the other five columns or the full
residual family after selecting the deficit column.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578ExteriorDensityCounterexample

open StructuralChargingNextState578UpperBracketFanCounterexample

set_option maxHeartbeats 24000000
set_option maxRecDepth 100000

/-- Five four-cups which avoid `capA`. -/
def selectedRow (i : Fin 5) : Finset (Fin 13) :=
  ![{1, 2, 5, 9},
    {1, 2, 7, 9},
    {1, 5, 7, 9},
    {1, 6, 8, 9},
    {5, 6, 7, 9}] i

/-- The distinct exterior source assigned to each selected row. -/
def selectedSource (i : Fin 5) : Fin 13 :=
  ![2, 1, 7, 6, 5] i

/-- The source cap column; columns one and two suffice in this local model. -/
def selectedSourceColumn (i : Fin 5) : Fin 3 :=
  ![2, 1, 2, 2, 1] i

/-- The explicit sweep-middle pair of each selected row. -/
def selectedMiddlePair (i : Fin 5) : Finset (Fin 13) :=
  ![{2, 5}, {2, 7}, {5, 7}, {6, 8}, {6, 7}] i

theorem selectedRow_turn_left (i : Fin 5) :
    turnSetBool (selectedRow i) .left = true := by
  fin_cases i <;> decide

theorem selectedRow_mem (i : Fin 5) :
    selectedRow i ∈ capWitnesses color.dual support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by fin_cases i <;> decide,
    by fin_cases i <;> decide, ?_⟩
  apply isCapSet_dual_iff.mpr
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff (selectedRow i) .left).mp
      (selectedRow_turn_left i)

theorem selectedRow_disjoint_blocker (i : Fin 5) :
    Disjoint (selectedRow i) capA := by
  fin_cases i <;> decide

theorem selectedSource_mem_row (i : Fin 5) :
    selectedSource i ∈ selectedRow i := by
  fin_cases i <;> decide

theorem selectedSource_mem_sourceCap (i : Fin 5) :
    selectedSource i ∈ capAt (selectedSourceColumn i) := by
  fin_cases i <;> decide

/-- Each selected cup is a valid source-private deletion row for its assigned
source column. -/
theorem selectedRow_inter_sourceCap (i : Fin 5) :
    selectedRow i ∩ capAt (selectedSourceColumn i) = {selectedSource i} := by
  fin_cases i <;> decide

theorem selectedSource_injective : Function.Injective selectedSource := by
  decide

theorem selectedSource_below_upper (i : Fin 5) :
    selectedSource i < (9 : Fin 13) := by
  fin_cases i <;> decide

theorem selectedRow_oneUpper (i : Fin 5) :
    CupFourOneUpperEndpointShape578 (selectedRow i) lower upper := by
  have hcupNode :
      selectedRow i ∈ capWitnesses color.dual (lower ∪ upper) 4 := by
    simpa [support] using selectedRow_mem i
  have hnotUpper : ¬selectedRow i ⊆ upper := by
    fin_cases i <;> decide
  have hnotLower : ¬selectedRow i ⊆ lower := by
    fin_cases i <;> decide
  have hshape : CupFourLowerEndpointShape578 (selectedRow i) lower upper :=
    ⟨(mem_capWitnesses.mp hcupNode).2.1,
      cupFour_deepSplit_upper_subset_endpoints root_deep hcupNode hnotUpper⟩
  exact hshape.oneUpper_of_upper_card_le_one
    (mem_capWitnesses.mp hcupNode).1 hnotLower (by decide)

/-- Every selected cup/blocker pair has its genuine first joint split at the
root used by the exterior fan. -/
theorem selectedRow_has_root_firstJoint_blocker (i : Fin 5) :
    ∃ joint : CupCapFirstJointSplit578 decompTree (selectedRow i) capA,
      joint.path = [] ∧ joint.node = rootNode := by
  fin_cases i <;>
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

theorem selectedMiddlePair_eq_sweepMiddlePair (i : Fin 5) :
    selectedMiddlePair i = sweepMiddlePair578 (selectedRow i)
      (mem_capWitnesses.mp (selectedRow_mem i)).2.1 := by
  fin_cases i
  · let hcard := (mem_capWitnesses.mp (selectedRow_mem (0 : Fin 5))).2.1
    let e := (selectedRow (0 : Fin 5)).orderEmbOfFin hcard
    have h0mem := (selectedRow (0 : Fin 5)).orderEmbOfFin_mem hcard 0
    have h1mem := (selectedRow (0 : Fin 5)).orderEmbOfFin_mem hcard 1
    have h2mem := (selectedRow (0 : Fin 5)).orderEmbOfFin_mem hcard 2
    have h3mem := (selectedRow (0 : Fin 5)).orderEmbOfFin_mem hcard 3
    have h01 := e.strictMono (show (0 : Fin 4) < 1 by decide)
    have h12 := e.strictMono (show (1 : Fin 4) < 2 by decide)
    have h23 := e.strictMono (show (2 : Fin 4) < 3 by decide)
    change e 0 ∈ selectedRow 0 at h0mem
    change e 1 ∈ selectedRow 0 at h1mem
    change e 2 ∈ selectedRow 0 at h2mem
    change e 3 ∈ selectedRow 0 at h3mem
    simp [selectedRow] at h0mem h1mem h2mem h3mem
    have h1eq : e 1 = 2 := by omega
    have h2eq : e 2 = 5 := by omega
    simp [selectedMiddlePair, sweepMiddlePair578, e, h1eq, h2eq]
  · let hcard := (mem_capWitnesses.mp (selectedRow_mem (1 : Fin 5))).2.1
    let e := (selectedRow (1 : Fin 5)).orderEmbOfFin hcard
    have h0mem := (selectedRow (1 : Fin 5)).orderEmbOfFin_mem hcard 0
    have h1mem := (selectedRow (1 : Fin 5)).orderEmbOfFin_mem hcard 1
    have h2mem := (selectedRow (1 : Fin 5)).orderEmbOfFin_mem hcard 2
    have h3mem := (selectedRow (1 : Fin 5)).orderEmbOfFin_mem hcard 3
    have h01 := e.strictMono (show (0 : Fin 4) < 1 by decide)
    have h12 := e.strictMono (show (1 : Fin 4) < 2 by decide)
    have h23 := e.strictMono (show (2 : Fin 4) < 3 by decide)
    change e 0 ∈ selectedRow 1 at h0mem
    change e 1 ∈ selectedRow 1 at h1mem
    change e 2 ∈ selectedRow 1 at h2mem
    change e 3 ∈ selectedRow 1 at h3mem
    simp [selectedRow] at h0mem h1mem h2mem h3mem
    have h1eq : e 1 = 2 := by omega
    have h2eq : e 2 = 7 := by omega
    simp [selectedMiddlePair, sweepMiddlePair578, e, h1eq, h2eq]
  · let hcard := (mem_capWitnesses.mp (selectedRow_mem (2 : Fin 5))).2.1
    let e := (selectedRow (2 : Fin 5)).orderEmbOfFin hcard
    have h0mem := (selectedRow (2 : Fin 5)).orderEmbOfFin_mem hcard 0
    have h1mem := (selectedRow (2 : Fin 5)).orderEmbOfFin_mem hcard 1
    have h2mem := (selectedRow (2 : Fin 5)).orderEmbOfFin_mem hcard 2
    have h3mem := (selectedRow (2 : Fin 5)).orderEmbOfFin_mem hcard 3
    have h01 := e.strictMono (show (0 : Fin 4) < 1 by decide)
    have h12 := e.strictMono (show (1 : Fin 4) < 2 by decide)
    have h23 := e.strictMono (show (2 : Fin 4) < 3 by decide)
    change e 0 ∈ selectedRow 2 at h0mem
    change e 1 ∈ selectedRow 2 at h1mem
    change e 2 ∈ selectedRow 2 at h2mem
    change e 3 ∈ selectedRow 2 at h3mem
    simp [selectedRow] at h0mem h1mem h2mem h3mem
    have h1eq : e 1 = 5 := by omega
    have h2eq : e 2 = 7 := by omega
    simp [selectedMiddlePair, sweepMiddlePair578, e, h1eq, h2eq]
  · let hcard := (mem_capWitnesses.mp (selectedRow_mem (3 : Fin 5))).2.1
    let e := (selectedRow (3 : Fin 5)).orderEmbOfFin hcard
    have h0mem := (selectedRow (3 : Fin 5)).orderEmbOfFin_mem hcard 0
    have h1mem := (selectedRow (3 : Fin 5)).orderEmbOfFin_mem hcard 1
    have h2mem := (selectedRow (3 : Fin 5)).orderEmbOfFin_mem hcard 2
    have h3mem := (selectedRow (3 : Fin 5)).orderEmbOfFin_mem hcard 3
    have h01 := e.strictMono (show (0 : Fin 4) < 1 by decide)
    have h12 := e.strictMono (show (1 : Fin 4) < 2 by decide)
    have h23 := e.strictMono (show (2 : Fin 4) < 3 by decide)
    change e 0 ∈ selectedRow 3 at h0mem
    change e 1 ∈ selectedRow 3 at h1mem
    change e 2 ∈ selectedRow 3 at h2mem
    change e 3 ∈ selectedRow 3 at h3mem
    simp [selectedRow] at h0mem h1mem h2mem h3mem
    have h1eq : e 1 = 6 := by omega
    have h2eq : e 2 = 8 := by omega
    simp [selectedMiddlePair, sweepMiddlePair578, e, h1eq, h2eq]
  · let hcard := (mem_capWitnesses.mp (selectedRow_mem (4 : Fin 5))).2.1
    let e := (selectedRow (4 : Fin 5)).orderEmbOfFin hcard
    have h0mem := (selectedRow (4 : Fin 5)).orderEmbOfFin_mem hcard 0
    have h1mem := (selectedRow (4 : Fin 5)).orderEmbOfFin_mem hcard 1
    have h2mem := (selectedRow (4 : Fin 5)).orderEmbOfFin_mem hcard 2
    have h3mem := (selectedRow (4 : Fin 5)).orderEmbOfFin_mem hcard 3
    have h01 := e.strictMono (show (0 : Fin 4) < 1 by decide)
    have h12 := e.strictMono (show (1 : Fin 4) < 2 by decide)
    have h23 := e.strictMono (show (2 : Fin 4) < 3 by decide)
    change e 0 ∈ selectedRow 4 at h0mem
    change e 1 ∈ selectedRow 4 at h1mem
    change e 2 ∈ selectedRow 4 at h2mem
    change e 3 ∈ selectedRow 4 at h3mem
    simp [selectedRow] at h0mem h1mem h2mem h3mem
    have h1eq : e 1 = 6 := by omega
    have h2eq : e 2 = 7 := by omega
    simp [selectedMiddlePair, sweepMiddlePair578, e, h1eq, h2eq]

/-- The five exact middle pairs have transversal number at least three. -/
theorem no_twoCover_selectedMiddlePairs :
    ¬∃ cover : Finset (Fin 13), cover.card ≤ 2 ∧
      ∀ i : Fin 5, ¬Disjoint (selectedMiddlePair i) cover := by
  decide

/-- Kernel-checked obstruction to the post-concentration *local* bridge. -/
theorem five_private_exterior_rows_miss_blocker_but_have_no_twoMiddleCover :
    IsDecomposable color ∧
    IsSweepRealizable color ∧
    HasDeepBelowSplit color lower upper ∧
    capA ∈ capWitnesses color support 4 ∧ capA ⊆ lower ∧
    Function.Injective selectedSource ∧
    (∀ i,
      selectedRow i ∈ capWitnesses color.dual support 4 ∧
      Disjoint (selectedRow i) capA ∧
      selectedSource i ∈ capAt (selectedSourceColumn i) ∧
      selectedRow i ∩ capAt (selectedSourceColumn i) =
        {selectedSource i} ∧
      selectedSource i < (9 : Fin 13) ∧
      CupFourOneUpperEndpointShape578 (selectedRow i) lower upper ∧
      ∃ joint : CupCapFirstJointSplit578 decompTree (selectedRow i) capA,
        joint.path = [] ∧ joint.node = rootNode) ∧
    (¬∃ cover : Finset (Fin 13), cover.card ≤ 2 ∧
      ∀ i : Fin 5,
        ¬Disjoint
          (sweepMiddlePair578 (selectedRow i)
            (mem_capWitnesses.mp (selectedRow_mem i)).2.1) cover) ∧
    ¬ContainsCupSet color support 5 ∧
    ¬ContainsCapSet color support 7 ∧
    ¬ContainsStrongPolygonSet color support 8 := by
  refine ⟨color_decomposable, color_sweepRealizable, root_deep,
    capAt_mem 0, capAt_subset_lower 0, selectedSource_injective,
    fun i ↦ ⟨selectedRow_mem i, selectedRow_disjoint_blocker i,
      selectedSource_mem_sourceCap i, selectedRow_inter_sourceCap i,
      selectedSource_below_upper i, selectedRow_oneUpper i,
      selectedRow_has_root_firstJoint_blocker i⟩, ?_,
    no_cup_five, no_cap_seven, no_strong_eight⟩
  intro hcover
  apply no_twoCover_selectedMiddlePairs
  obtain ⟨cover, hcard, hhits⟩ := hcover
  refine ⟨cover, hcard, fun i ↦ ?_⟩
  rw [selectedMiddlePair_eq_sweepMiddlePair]
  exact hhits i

end StructuralChargingNextState578ExteriorDensityCounterexample
end ErdosSzekeres

end
