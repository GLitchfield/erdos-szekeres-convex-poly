module

public import ErdosSzekeres.HMPTVerticalChainDefs
public import ErdosSzekeres.PorValtrSupportProduct
public import ErdosSzekeres.SukRegionChainGeometry

@[expose] public section

/-!
# Cyclic HMPT spike geometry

This module records the cyclic source projection requested by the second HMPT
layer.  The frozen lower bound `2 ≤ r` admits a four-anchor support, for which
the five consecutive anchors in every adjacent geometry repeat an endpoint.
The exact rational construction below certifies that obstruction.
-/

namespace ErdosSzekeres

noncomputable section

/-- The next index in the cyclic family of `2 * r` spike pools. -/
def hmptCyclicSucc {r : ℕ} (i : Fin (2 * r)) : Fin (2 * r) :=
  ⟨(i.1 + 1) % (2 * r), Nat.mod_lt _
    (lt_of_le_of_lt (Nat.zero_le i.1) i.2)⟩

namespace PorValtrSupportProductData

/-- The exact cyclic source pool at a finite support index. -/
def hmptPool {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (i : Fin (2 * r)) :
    Finset (Point 2) :=
  h.sourcePool i.1

/-- Five consecutive cyclic anchors, starting with the predecessor of `i`. -/
def hmptAnchor {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (i : Fin (2 * r))
    (offset : Fin 5) : Point 2 :=
  h.anchors ((i.1 + (2 * r - 1) + offset.1) % (2 * r))

end PorValtrSupportProductData

/-- The full cyclic source geometry required by the HMPT vertical-chain layer. -/
structure HMPTCyclicSpikeGeometry
    (P : Finset (Point 2)) (r : ℕ)
    (h : PorValtrSupportProductData P r) : Prop where
  pool_subset : ∀ i : Fin (2 * r), h.hmptPool i ⊆ P
  pools_disjoint : ∀ i j : Fin (2 * r), i ≠ j →
    Disjoint (h.hmptPool i) (h.hmptPool j)
  localRegion : ∀ i : Fin (2 * r),
    SukRegionGeometry (h.hmptAnchor i 0) (h.hmptAnchor i 1)
      (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i)
  adjacentGeometry : ∀ i : Fin (2 * r),
    HMPTAdjacentSpikeGeometry (h.hmptAnchor i 0) (h.hmptAnchor i 1)
      (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptAnchor i 4)
      (h.hmptPool i) (h.hmptPool (hmptCyclicSucc i))

namespace HMPTCyclicSourceCounterexample

private def a0 : Point 2 := ![0, 0]
private def a1 : Point 2 := ![1, 3]
private def a2 : Point 2 := ![2, 4]
private def a3 : Point 2 := ![3, 3]

private def point : Fin 4 → Point 2 := ![a0, a1, a2, a3]

private def anchors (i : ℕ) : Point 2 :=
  point ⟨i % 4, Nat.mod_lt _ (by decide)⟩

private def carrier : Finset (Point 2) := {a0, a1, a2, a3}

private def sourcePool (_i : ℕ) : Finset (Point 2) := ∅

private theorem anchors_strictCap : SukStrictCapSequence 4 anchors := by
  intro i j k hij hjk hk
  have hi : i < 4 := by omega
  have hj : j < 4 := by omega
  interval_cases i <;> interval_cases j <;> interval_cases k <;>
    norm_num [anchors, point, a0, a1, a2, a3, orientation] at *

private theorem anchors_periodic (i : ℕ) : anchors (i + 4) = anchors i := by
  unfold anchors
  apply congrArg point
  apply Fin.ext
  simp

private theorem anchor_mem (i : ℕ) (hi : i < 4) : anchors i ∈ carrier := by
  interval_cases i <;> simp [anchors, point, carrier]

private theorem cyclicOpenPool_eq_empty (i : ℕ) (hi : i < 4) :
    porValtrCyclicOpenPool carrier 4 anchors i = ∅ := by
  ext p
  simp only [Finset.notMem_empty, iff_false]
  intro hp
  have hp' : p ∈ carrier ∧ p ∈ porValtrCyclicOpenCell 4 anchors i := by
    simpa [porValtrCyclicOpenPool] using hp
  rcases hp' with ⟨hpCarrier, hpCell⟩
  simp only [carrier, Finset.mem_insert, Finset.mem_singleton] at hpCarrier
  interval_cases i <;>
    rcases hpCarrier with rfl | rfl | rfl | rfl <;>
      norm_num [porValtrCyclicOpenCell, SukSupportRegion, anchors, point,
        a0, a1, a2, a3, orientation] at hpCell

private theorem carrier_card : carrier.card = 4 := by
  norm_num [carrier, a0, a1, a2, a3]

/-- The smallest cyclic support datum admitted by the frozen `2 ≤ r` premise. -/
private def data : PorValtrSupportProductData carrier 2 where
  anchors := anchors
  sourcePool := sourcePool
  strictCap := by simpa using anchors_strictCap
  periodic := by
    intro i
    simpa using anchors_periodic i
  anchorsSubset := by
    intro i hi
    exact anchor_mem i (by omega)
  sourcePool_eq := by
    intro i hi
    simpa [sourcePool] using (cyclicOpenPool_eq_empty i (by omega)).symm
  sourcePoolsDisjoint := by
    intro i _hi j _hj _hij
    change Disjoint (∅ : Finset (Point 2)) ∅
    exact Finset.disjoint_empty_left ∅
  productBound := by
    rw [carrier_card]
    norm_num [sourcePool]

/-- The four rational anchors are in general position. -/
private theorem generalPosition : InGeneralPosition carrier := by
  intro x hx y hy z hz hxy hxz hyz
  simp only [carrier, Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl | rfl <;>
        norm_num [orientation, a0, a1, a2, a3] at *

/-- At `r = 2`, the last-to-first adjacent five-anchor block repeats its two
outer endpoints, contradicting its strict-cap field. -/
private theorem no_cyclicSpikeGeometry :
    ¬HMPTCyclicSpikeGeometry carrier 2 data := by
  intro hgeometry
  let last : Fin (2 * 2) := ⟨3, by omega⟩
  have hwrap : hmptCyclicSucc last = 0 := by
    apply Fin.ext
    norm_num [hmptCyclicSucc, last]
  have hadjacent := hgeometry.adjacentGeometry last
  rw [hwrap] at hadjacent
  have hrepeat : data.hmptAnchor last 4 = data.hmptAnchor last 0 := by
    norm_num [PorValtrSupportProductData.hmptAnchor, last]
  have hstrict := hadjacent.anchorsCap.orient014
  rw [hrepeat] at hstrict
  simp [orientation] at hstrict

/-- A kernel-level witness that the frozen `2 ≤ r` cyclic source contract is
false on an inhabited, general-position support-product source. -/
theorem frozenContract_false :
    ¬(∀ {P : Finset (Point 2)} {r : ℕ},
      (h : PorValtrSupportProductData P r) →
      2 ≤ r → InGeneralPosition P → HMPTCyclicSpikeGeometry P r h) := by
  intro hcontract
  exact no_cyclicSpikeGeometry (hcontract data (by decide) generalPosition)

end HMPTCyclicSourceCounterexample

end

end ErdosSzekeres

end
