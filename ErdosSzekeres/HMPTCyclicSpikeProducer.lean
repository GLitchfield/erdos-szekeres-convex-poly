module

public import ErdosSzekeres.HMPTCyclicSpikeGeometry

@[expose] public section

/-!
# HMPT cyclic spike geometry producer

This module projects Pór--Valtr support-product data onto the cyclic spike
geometry used by the HMPT vertical-profile layer.
-/

namespace ErdosSzekeres

noncomputable section

private theorem hmptProducer_cyclic_orientation_neg
    {m : ℕ} {anchors : ℕ → Point 2}
    (hcap : SukStrictCapSequence m anchors)
    {i j k : ℕ} (hi : i < m) (hj : j < m) (hk : k < m)
    (hcyclic :
      (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)) :
    orientation (anchors i) (anchors j) (anchors k) < 0 := by
  rcases hcyclic with hijk | hjki | hkij
  · exact hcap hijk.1 hijk.2 hk
  · have h := hcap hjki.1 hjki.2 hi
    rw [orientation_cyclic (anchors i) (anchors j) (anchors k)] at h
    exact h
  · have h := hcap hkij.1 hkij.2 hj
    rw [orientation_cyclic' (anchors i) (anchors j) (anchors k)] at h
    exact h

private theorem hmptProducer_strictCap_rotate
    {m s : ℕ} {anchors : ℕ → Point 2}
    (_hm : 0 < m) (hs : s < m)
    (hcap : SukStrictCapSequence m anchors) :
    SukStrictCapSequence m (fun i ↦ anchors ((s + i) % m)) := by
  intro a b c hab hbc hc
  have ha : a < m := by omega
  have hb : b < m := by omega
  have hsa : s + a < 2 * m := by omega
  have hsb : s + b < 2 * m := by omega
  have hsc : s + c < 2 * m := by omega
  change orientation (anchors ((s + a) % m))
    (anchors ((s + b) % m)) (anchors ((s + c) % m)) < 0
  by_cases hcm : s + c < m
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt hcm]
    exact hmptProducer_cyclic_orientation_neg hcap
      (by omega) (by omega) hcm (Or.inl ⟨by omega, by omega⟩)
  by_cases hbm : s + b < m
  · have hca : (s + c) % m = s + c - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hbm, hca]
    exact hmptProducer_cyclic_orientation_neg hcap
      (by omega) hbm (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))
  by_cases ham : s + a < m
  · have hba : (s + b) % m = s + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hca : (s + c) % m = s + c - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt ham, hba, hca]
    exact hmptProducer_cyclic_orientation_neg hcap
      ham (by omega) (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · have haa : (s + a) % m = s + a - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hba : (s + b) % m = s + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hca : (s + c) % m = s + c - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [haa, hba, hca]
    exact hmptProducer_cyclic_orientation_neg hcap
      (by omega) (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)

private theorem hmptProducer_anchors_mod
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (_hr : 3 ≤ r)
    {t : ℕ} (ht : t < 2 * (2 * r)) :
    h.anchors (t % (2 * r)) = h.anchors t := by
  by_cases htPeriod : t < 2 * r
  · rw [Nat.mod_eq_of_lt htPeriod]
  · have hsub : t - 2 * r < 2 * r := by omega
    have htEq : t = (t - 2 * r) + 2 * r := by omega
    rw [htEq, h.periodic (t - 2 * r)]
    simp only [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_eq_of_lt hsub]

private theorem hmptProducer_anchor_eq_of_pos
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) (offset : Fin 5) (hoffset : 0 < offset.1) :
    h.hmptAnchor i offset = h.anchors (i.1 + offset.1 - 1) := by
  have hbound : i.1 + offset.1 - 1 < 2 * (2 * r) := by omega
  have hsum : i.1 + (2 * r - 1) + offset.1 =
      2 * r + (i.1 + offset.1 - 1) := by
    omega
  unfold PorValtrSupportProductData.hmptAnchor
  rw [hsum]
  simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  exact hmptProducer_anchors_mod h hr hbound

private theorem hmptProducer_anchor_one
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) :
    h.hmptAnchor i 1 = h.anchors i.1 := by
  simpa using hmptProducer_anchor_eq_of_pos h hr i (1 : Fin 5) (by decide)

private theorem hmptProducer_anchor_two
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) :
    h.hmptAnchor i 2 = h.anchors (i.1 + 1) := by
  convert hmptProducer_anchor_eq_of_pos h hr i (2 : Fin 5) (by decide) using 1

private theorem hmptProducer_anchor_three
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) :
    h.hmptAnchor i 3 = h.anchors (i.1 + 2) := by
  convert hmptProducer_anchor_eq_of_pos h hr i (3 : Fin 5) (by decide) using 1

private theorem hmptProducer_anchor_four
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) :
    h.hmptAnchor i 4 = h.anchors (i.1 + 3) := by
  convert hmptProducer_anchor_eq_of_pos h hr i (4 : Fin 5) (by decide) using 1

private theorem hmptProducer_anchor_zero_of_eq_zero
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) (hi : i.1 = 0) :
    h.hmptAnchor i 0 = h.anchors (2 * r - 1) := by
  unfold PorValtrSupportProductData.hmptAnchor
  simp only [Fin.val_zero, Nat.add_zero, hi, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (by omega : 2 * r - 1 < 2 * r)]

private theorem hmptProducer_anchor_zero_of_pos
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) (hi : 0 < i.1) :
    h.hmptAnchor i 0 = h.anchors (i.1 - 1) := by
  unfold PorValtrSupportProductData.hmptAnchor
  simp only [Fin.val_zero, Nat.add_zero]
  have hsum : i.1 + (2 * r - 1) = 2 * r + (i.1 - 1) := by omega
  rw [hsum]
  simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  rw [Nat.mod_eq_of_lt (by omega : i.1 - 1 < 2 * r)]

private theorem hmptProducer_fiveCap
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) :
    SukFiveCapAnchors (h.hmptAnchor i 0) (h.hmptAnchor i 1)
      (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptAnchor i 4) := by
  let s := (i.1 + (2 * r - 1)) % (2 * r)
  have hs : s < 2 * r := Nat.mod_lt _ (by omega)
  have hrot : SukStrictCapSequence (2 * r)
      (fun k ↦ h.anchors ((s + k) % (2 * r))) :=
    hmptProducer_strictCap_rotate (by omega) hs h.strictCap
  have hanchor (offset : Fin 5) :
      h.hmptAnchor i offset =
        h.anchors ((s + offset.1) % (2 * r)) := by
    unfold PorValtrSupportProductData.hmptAnchor
    apply congrArg h.anchors
    dsimp only [s]
    exact (Nat.mod_add_mod (i.1 + (2 * r - 1)) (2 * r) offset.1).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hanchor] using
      (hrot (i := 0) (j := 1) (k := 2) (by omega) (by omega) (by omega))
  · simpa only [hanchor] using
      (hrot (i := 0) (j := 1) (k := 3) (by omega) (by omega) (by omega))
  · simpa only [hanchor] using
      (hrot (i := 0) (j := 1) (k := 4) (by omega) (by omega) (by omega))
  · simpa only [hanchor] using
      (hrot (i := 0) (j := 2) (k := 3) (by omega) (by omega) (by omega))
  · simpa only [hanchor] using
      (hrot (i := 0) (j := 2) (k := 4) (by omega) (by omega) (by omega))
  · simpa only [hanchor] using
      (hrot (i := 0) (j := 3) (k := 4) (by omega) (by omega) (by omega))
  · simpa only [hanchor] using
      (hrot (i := 1) (j := 2) (k := 3) (by omega) (by omega) (by omega))
  · simpa only [hanchor] using
      (hrot (i := 1) (j := 2) (k := 4) (by omega) (by omega) (by omega))
  · simpa only [hanchor] using
      (hrot (i := 1) (j := 3) (k := 4) (by omega) (by omega) (by omega))
  · simpa only [hanchor] using
      (hrot (i := 2) (j := 3) (k := 4) (by omega) (by omega) (by omega))

private theorem hmptProducer_pool_subset
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (i : Fin (2 * r)) :
    h.hmptPool i ⊆ P := by
  classical
  change h.sourcePool i.1 ⊆ P
  rw [h.sourcePool_eq i.1 i.2]
  exact Finset.filter_subset _ _

private theorem hmptProducer_anchor_mem
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) (offset : Fin 5) :
    h.hmptAnchor i offset ∈ P := by
  unfold PorValtrSupportProductData.hmptAnchor
  exact h.anchorsSubset _ (Nat.mod_lt _ (by omega))

private theorem hmptProducer_openCell_eq
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) :
    porValtrCyclicOpenCell (2 * r) h.anchors i.1 =
      SukSupportRegion (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) := by
  rw [hmptProducer_anchor_one h hr i, hmptProducer_anchor_two h hr i,
    hmptProducer_anchor_three h hr i]
  by_cases hi : i.1 = 0
  · rw [hmptProducer_anchor_zero_of_eq_zero h hr i hi]
    simp [porValtrCyclicOpenCell, hi]
  · have hiPos : 0 < i.1 := by omega
    rw [hmptProducer_anchor_zero_of_pos h hr i hiPos]
    simp only [porValtrCyclicOpenCell, if_neg hi]

private def hmptProducer_localGeometry
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (hgp : InGeneralPosition P) (i : Fin (2 * r)) :
    SukRegionGeometry (h.hmptAnchor i 0) (h.hmptAnchor i 1)
      (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i) where
  anchorsCap := (hmptProducer_fiveCap h hr i).leftFour
  generalPosition := by
    apply hgp.mono
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | rfl | rfl | rfl | hp
    · exact hmptProducer_anchor_mem h hr i 0
    · exact hmptProducer_anchor_mem h hr i 1
    · exact hmptProducer_anchor_mem h hr i 2
    · exact hmptProducer_anchor_mem h hr i 3
    · exact hmptProducer_pool_subset h i hp
  region := by
    classical
    intro p hp
    have hpCell : p ∈ porValtrCyclicOpenCell (2 * r) h.anchors i.1 := by
      change p ∈ h.sourcePool i.1 at hp
      rw [h.sourcePool_eq i.1 i.2] at hp
      exact (Finset.mem_filter.mp hp).2
    rw [hmptProducer_openCell_eq h hr i] at hpCell
    exact hpCell

private theorem hmptProducer_succ_ne
    {r : ℕ} (_hr : 3 ≤ r) (i : Fin (2 * r)) :
    i ≠ hmptCyclicSucc i := by
  intro hi
  have hval := congrArg Fin.val hi
  simp only [hmptCyclicSucc, Fin.val_mk] at hval
  by_cases hnext : i.1 + 1 < 2 * r
  · rw [Nat.mod_eq_of_lt hnext] at hval
    omega
  · have hlast : i.1 + 1 = 2 * r := by omega
    rw [hlast, Nat.mod_self] at hval
    omega

private theorem hmptProducer_anchor_succ
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (_hr : 3 ≤ r)
    (i : Fin (2 * r)) (offset : ℕ) (hoffset : offset + 1 < 5) :
    h.hmptAnchor (hmptCyclicSucc i) ⟨offset, by omega⟩ =
      h.hmptAnchor i ⟨offset + 1, hoffset⟩ := by
  unfold PorValtrSupportProductData.hmptAnchor hmptCyclicSucc
  apply congrArg h.anchors
  calc
    ((i.1 + 1) % (2 * r) + (2 * r - 1) + offset) % (2 * r) =
        (i.1 + 1 + (2 * r - 1 + offset)) % (2 * r) := by
      rw [Nat.add_assoc, Nat.mod_add_mod]
    _ = (i.1 + (2 * r - 1) + (offset + 1)) % (2 * r) := by
      congr 1
      omega

private theorem hmptProducer_pools_disjoint
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (i : Fin (2 * r)) :
    Disjoint (h.hmptPool i) (h.hmptPool (hmptCyclicSucc i)) := by
  change Disjoint (h.sourcePool i.1)
    (h.sourcePool (hmptCyclicSucc i).1)
  apply h.sourcePoolsDisjoint i.1 i.2
    (hmptCyclicSucc i).1 (hmptCyclicSucc i).2
  intro hval
  apply hmptProducer_succ_ne hr i
  apply Fin.ext
  exact hval

private def hmptProducer_adjacentGeometry
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (hgp : InGeneralPosition P) (i : Fin (2 * r)) :
    HMPTAdjacentSpikeGeometry (h.hmptAnchor i 0) (h.hmptAnchor i 1)
      (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptAnchor i 4)
      (h.hmptPool i) (h.hmptPool (hmptCyclicSucc i)) where
  anchorsCap := hmptProducer_fiveCap h hr i
  disjoint := hmptProducer_pools_disjoint h hr i
  generalPosition := by
    apply hgp.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | hp | hp
    · exact hmptProducer_anchor_mem h hr i 0
    · exact hmptProducer_anchor_mem h hr i 1
    · exact hmptProducer_anchor_mem h hr i 2
    · exact hmptProducer_anchor_mem h hr i 3
    · exact hmptProducer_anchor_mem h hr i 4
    · exact hmptProducer_pool_subset h i hp
    · exact hmptProducer_pool_subset h (hmptCyclicSucc i) hp
  leftRegion := by
    intro p hp
    exact (hmptProducer_localGeometry h hr hgp i).region hp
  rightRegion := by
    intro p hp
    have hpRegion :=
      (hmptProducer_localGeometry h hr hgp (hmptCyclicSucc i)).region hp
    have h0 : h.hmptAnchor (hmptCyclicSucc i) 0 = h.hmptAnchor i 1 :=
      hmptProducer_anchor_succ h hr i 0 (by decide)
    have h1 : h.hmptAnchor (hmptCyclicSucc i) 1 = h.hmptAnchor i 2 :=
      hmptProducer_anchor_succ h hr i 1 (by decide)
    have h2 : h.hmptAnchor (hmptCyclicSucc i) 2 = h.hmptAnchor i 3 :=
      hmptProducer_anchor_succ h hr i 2 (by decide)
    have h3 : h.hmptAnchor (hmptCyclicSucc i) 3 = h.hmptAnchor i 4 :=
      hmptProducer_anchor_succ h hr i 3 (by decide)
    rw [h0, h1, h2, h3] at hpRegion
    exact hpRegion

namespace PorValtrSupportProductData

/-- A support-product datum at the reachable endpoint produces the complete
cyclic spike geometry on its original carrier. -/
theorem toHMPTCyclicSpikeGeometry
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r)
    (hr : 3 ≤ r)
    (hgp : InGeneralPosition P) :
    HMPTCyclicSpikeGeometry P r h where
  pool_subset := hmptProducer_pool_subset h
  pools_disjoint := by
    intro i j hij
    change Disjoint (h.sourcePool i.1) (h.sourcePool j.1)
    apply h.sourcePoolsDisjoint i.1 i.2 j.1 j.2
    intro hval
    apply hij
    exact Fin.ext hval
  localRegion := hmptProducer_localGeometry h hr hgp
  adjacentGeometry := hmptProducer_adjacentGeometry h hr hgp

end PorValtrSupportProductData

end

end ErdosSzekeres

end
