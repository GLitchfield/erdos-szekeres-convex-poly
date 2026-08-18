module

public import ErdosSzekeres.HMPTCyclicSpikeProducer
public import ErdosSzekeres.PorValtrCyclicSupportBridge

@[expose] public section

/-!
# Cyclic horizontal separation for HMPT spike pools

Same-parity distinct support pools are nonadjacent on the cyclic support.  A
rotation places them in a linear strict-cap window, where support-cell
contraction supplies both the remote horizontal-pair separator and the local
base-edge separator.  The reverse rotation is used for cyclic distance
`2 * r - 2`, including the wrap pairs when `r = 3`.
-/

namespace ErdosSzekeres

noncomputable section

private theorem hmptSeparation_orientation_plucker
    (a b c d e : Point 2) :
    orientation a b c * orientation a d e -
      orientation a b d * orientation a c e +
      orientation a b e * orientation a c d = 0 := by
  simp only [orientation]
  ring

private theorem hmptSeparation_support_left_diagonal_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (hcdp : orientation c d p < 0) :
    0 < orientation a c p := by
  have hplucker := hmptSeparation_orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

private theorem hmptSeparation_support_base_orientation_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (habd : orientation a b d < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (habp : orientation a b p < 0)
    (hcdp : orientation c d p < 0) :
    0 < orientation a d p := by
  have hpluckerC := hmptSeparation_orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p, orientation_swap b c d] at hpluckerC
  have hcap : orientation c a p < 0 := by
    nlinarith
  have hacp : 0 < orientation a c p := by
    rw [orientation_swap a c p] at hcap
    linarith
  have hpluckerA := hmptSeparation_orientation_plucker a b c d p
  nlinarith

private theorem hmptSeparation_cyclic_orientation_neg
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

private theorem hmptSeparation_strictCap_rotate
    {m start : ℕ} {anchors : ℕ → Point 2}
    (_hm : 0 < m) (hstart : start < m)
    (hcap : SukStrictCapSequence m anchors) :
    SukStrictCapSequence m (fun i ↦ anchors ((start + i) % m)) := by
  intro a b c hab hbc hc
  have ha : a < m := by omega
  have hb : b < m := by omega
  have hsa : start + a < 2 * m := by omega
  have hsb : start + b < 2 * m := by omega
  have hsc : start + c < 2 * m := by omega
  change orientation (anchors ((start + a) % m))
    (anchors ((start + b) % m)) (anchors ((start + c) % m)) < 0
  by_cases hcm : start + c < m
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt hcm]
    exact hmptSeparation_cyclic_orientation_neg hcap
      (by omega) (by omega) hcm (Or.inl ⟨by omega, by omega⟩)
  by_cases hbm : start + b < m
  · have hca : (start + c) % m = start + c - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hbm, hca]
    exact hmptSeparation_cyclic_orientation_neg hcap
      (by omega) hbm (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))
  by_cases ham : start + a < m
  · have hba : (start + b) % m = start + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hca : (start + c) % m = start + c - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt ham, hba, hca]
    exact hmptSeparation_cyclic_orientation_neg hcap
      ham (by omega) (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · have haa : (start + a) % m = start + a - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hba : (start + b) % m = start + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hca : (start + c) % m = start + c - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [haa, hba, hca]
    exact hmptSeparation_cyclic_orientation_neg hcap
      (by omega) (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)

private def hmptSeparationIndex
    {r : ℕ} (hr : 3 ≤ r) (start : Fin (2 * r)) (k : ℕ) :
    Fin (2 * r) :=
  ⟨(start.val + k) % (2 * r), Nat.mod_lt _ (by omega)⟩

private def hmptSeparationAnchor
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (_hr : 3 ≤ r)
    (start : Fin (2 * r)) (k : ℕ) : Point 2 :=
  h.anchors (((start.val + (2 * r - 1)) % (2 * r) + k) % (2 * r))

private def hmptSeparationPool
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (start : Fin (2 * r)) (k : ℕ) : Finset (Point 2) :=
  h.hmptPool (hmptSeparationIndex hr start k)

private theorem hmptSeparationAnchor_eq_hmptAnchor
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (start : Fin (2 * r)) (k : ℕ) (offset : Fin 5) :
    hmptSeparationAnchor h hr start (k + offset.val) =
      h.hmptAnchor (hmptSeparationIndex hr start k) offset := by
  unfold hmptSeparationAnchor PorValtrSupportProductData.hmptAnchor
    hmptSeparationIndex
  apply congrArg h.anchors
  calc
    ((start.val + (2 * r - 1)) % (2 * r) +
          (k + offset.val)) % (2 * r) =
        (start.val + (2 * r - 1) + (k + offset.val)) % (2 * r) := by
          rw [Nat.mod_add_mod]
    _ = (start.val + k + ((2 * r - 1) + offset.val)) % (2 * r) := by
      congr 1
      omega
    _ = ((start.val + k) % (2 * r) +
          (2 * r - 1) + offset.val) % (2 * r) := by
      rw [show (start.val + k) % (2 * r) + (2 * r - 1) + offset.val =
        (start.val + k) % (2 * r) + ((2 * r - 1) + offset.val) by omega,
        Nat.mod_add_mod]

private theorem hmptSeparation_succ_ne
    {r : ℕ} (_hr : 3 ≤ r) (i : Fin (2 * r)) :
    i ≠ hmptCyclicSucc i := by
  intro hi
  have hval := congrArg Fin.val hi
  simp only [hmptCyclicSucc, Fin.val_mk] at hval
  by_cases hnext : i.val + 1 < 2 * r
  · rw [Nat.mod_eq_of_lt hnext] at hval
    omega
  · have hlast : i.val + 1 = 2 * r := by omega
    rw [hlast, Nat.mod_self] at hval
    omega

private theorem hmptSeparationIndex_succ
    {r : ℕ} (hr : 3 ≤ r) (start : Fin (2 * r)) (k : ℕ) :
    hmptSeparationIndex hr start (k + 1) =
      hmptCyclicSucc (hmptSeparationIndex hr start k) := by
  apply Fin.ext
  change (start.val + (k + 1)) % (2 * r) =
    (((start.val + k) % (2 * r) + 1) % (2 * r))
  rw [show start.val + (k + 1) = start.val + k + 1 by omega,
    Nat.mod_add_mod]

private theorem hmptSeparationPool_eq
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (start : Fin (2 * r)) (k : ℕ) (i : Fin (2 * r))
    (hki : (start.val + k) % (2 * r) = i.val) :
    hmptSeparationPool h hr start k = h.hmptPool i := by
  have hindex : hmptSeparationIndex hr start k = i := Fin.ext hki
  simp [hmptSeparationPool, hindex]

private theorem hmptSeparationAnchor_eq
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (start : Fin (2 * r)) (k : ℕ) (i : Fin (2 * r))
    (hki : (start.val + k) % (2 * r) = i.val) (offset : Fin 5) :
    hmptSeparationAnchor h hr start (k + offset.val) =
      h.hmptAnchor i offset := by
  rw [hmptSeparationAnchor_eq_hmptAnchor]
  exact congrArg (fun u : Fin (2 * r) ↦ h.hmptAnchor u offset)
    (Fin.ext hki)

private theorem hmptSeparation_window
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (hgp : InGeneralPosition P) (start : Fin (2 * r)) :
    SukConsecutiveRawPools (2 * r - 3)
      (hmptSeparationAnchor h hr start)
      (hmptSeparationPool h hr start) := by
  let geometry := h.toHMPTCyclicSpikeGeometry hr hgp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hstart : (start.val + (2 * r - 1)) % (2 * r) < 2 * r :=
      Nat.mod_lt _ (by omega)
    have hrotate := hmptSeparation_strictCap_rotate
      (by omega : 0 < 2 * r) hstart h.strictCap
    rw [show 2 * r - 3 + 3 = 2 * r by omega]
    change SukStrictCapSequence (2 * r)
      (fun k ↦ h.anchors
        (((start.val + (2 * r - 1)) % (2 * r) + k) % (2 * r)))
    exact hrotate
  · intro k hk
    change Disjoint
      (h.hmptPool (hmptSeparationIndex hr start k))
      (h.hmptPool (hmptSeparationIndex hr start (k + 1)))
    rw [hmptSeparationIndex_succ hr start k]
    exact geometry.pools_disjoint _ _
      (hmptSeparation_succ_ne hr (hmptSeparationIndex hr start k))
  · apply hgp.mono
    intro p hp
    rcases Finset.mem_union.mp hp with hpAnchor | hpPool
    · rcases Finset.mem_image.mp hpAnchor with ⟨k, hk, rfl⟩
      unfold hmptSeparationAnchor
      exact h.anchorsSubset _ (Nat.mod_lt _ (by omega))
    · rcases Finset.mem_biUnion.mp hpPool with ⟨k, hk, hp⟩
      exact geometry.pool_subset (hmptSeparationIndex hr start k) hp
  · intro k hk p hp
    have hregion :=
      (geometry.localRegion (hmptSeparationIndex hr start k)).region hp
    rw [← hmptSeparationAnchor_eq_hmptAnchor h hr start k (0 : Fin 5),
      ← hmptSeparationAnchor_eq_hmptAnchor h hr start k (1 : Fin 5),
      ← hmptSeparationAnchor_eq_hmptAnchor h hr start k (2 : Fin 5),
      ← hmptSeparationAnchor_eq_hmptAnchor h hr start k (3 : Fin 5)] at hregion
    simpa using hregion

private theorem SukConsecutiveRawPools.hmptSeparation_contractedRegion
    {L : ℕ} {anchors : ℕ → Point 2}
    {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {i a b c d : ℕ} (hi : i < L) {p : Point 2} (hp : p ∈ pools i)
    (hab : a < b) (hbi : b ≤ i + 1) (hic : i + 2 ≤ c)
    (hcd : c < d) (hd : d < L + 3) :
    p ∈ SukSupportRegion
      (anchors a) (anchors b) (anchors c) (anchors d) := by
  apply sukSupportRegion_subset_of_strictCapBlock
    (L + 3) a b c d i anchors hraw.strictCap hab hbi hic hcd hd
  exact hraw.region i hi hp

private theorem SukConsecutiveRawPools.hmptSeparation_remote_sameStrictSide
    {L : ℕ} {anchors : ℕ → Point 2}
    {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (i j : Fin L)
    (hseparated : i.val + 1 < j.val ∨ j.val + 1 < i.val)
    {p q z : Point 2}
    (hp : p ∈ pools i.val) (_hq : q ∈ pools i.val)
    (hz : z ∈ pools j.val)
    (hside : SameStrictSide p q
      (anchors i.val) (anchors (i.val + 3))) :
    SameStrictSide p q (anchors i.val) z := by
  let A := anchors i.val
  let B := anchors (i.val + 1)
  let C := anchors (i.val + 2)
  let D := anchors (i.val + 3)
  have hABC : orientation A B C < 0 :=
    hraw.strictCap (by omega) (by omega) (by omega)
  have hABD : orientation A B D < 0 :=
    hraw.strictCap (by omega) (by omega) (by omega)
  have hACD : orientation A C D < 0 :=
    hraw.strictCap (by omega) (by omega) (by omega)
  have hBCD : orientation B C D < 0 :=
    hraw.strictCap (by omega) (by omega) (by omega)
  have hpRegion := hraw.region i.val i.isLt hp
  have hACp : 0 < orientation A C p :=
    hmptSeparation_support_left_diagonal_pos A B C D p
      hABC hACD hBCD hpRegion.1 hpRegion.2.2
  have hADp : 0 < orientation A D p :=
    hmptSeparation_support_base_orientation_pos A B C D p
      hABC hABD hACD hBCD hpRegion.1 hpRegion.2.1 hpRegion.2.2
  have hzSigns : orientation A B z < 0 ∧ orientation A C z < 0 ∧
      orientation A D z < 0 ∧ orientation C D z < 0 := by
    rcases hseparated with hij | hji
    · refine ⟨
        (hraw.hmptSeparation_contractedRegion j.isLt hz
          (a := i.val) (b := i.val + 1) (c := j.val + 2)
          (d := j.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.1,
        (hraw.hmptSeparation_contractedRegion j.isLt hz
          (a := i.val) (b := i.val + 2) (c := j.val + 2)
          (d := j.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.1,
        (hraw.hmptSeparation_contractedRegion j.isLt hz
          (a := i.val) (b := i.val + 3) (c := j.val + 2)
          (d := j.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.1,
        (hraw.hmptSeparation_contractedRegion j.isLt hz
          (a := i.val + 2) (b := i.val + 3) (c := j.val + 2)
          (d := j.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.1⟩
    · refine ⟨
        (hraw.hmptSeparation_contractedRegion j.isLt hz
          (a := j.val) (b := j.val + 1) (c := i.val) (d := i.val + 1)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.2,
        (hraw.hmptSeparation_contractedRegion j.isLt hz
          (a := j.val) (b := j.val + 1) (c := i.val) (d := i.val + 2)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.2,
        (hraw.hmptSeparation_contractedRegion j.isLt hz
          (a := j.val) (b := j.val + 1) (c := i.val) (d := i.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.2,
        (hraw.hmptSeparation_contractedRegion j.isLt hz
          (a := j.val) (b := j.val + 1) (c := i.val + 2)
          (d := i.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.2⟩
  have hApz : orientation A p z < 0 := by
    have hplucker := hmptSeparation_orientation_plucker A B C p z
    nlinarith [hpRegion.2.1, hACp, hzSigns.1, hzSigns.2.1]
  have hDpz : 0 < orientation D p z := by
    have hDac : orientation D A C < 0 := by
      rw [orientation_cyclic' A C D]
      exact hACD
    have hDap : orientation D A p < 0 := by
      rw [orientation_cyclic' A p D, orientation_swap_last A D p]
      linarith
    have hDcz : 0 < orientation D C z := by
      rw [orientation_swap C D z]
      linarith [hzSigns.2.2.2]
    have hDaz : 0 < orientation D A z := by
      rw [orientation_cyclic' A z D, orientation_swap_last A D z]
      linarith [hzSigns.2.2.1]
    have hDcp : 0 < orientation D C p := by
      rw [orientation_swap C D p]
      linarith [hpRegion.2.2]
    have hplucker := hmptSeparation_orientation_plucker D A C p z
    nlinarith
  have hpDz : orientation p D z < 0 := by
    rw [orientation_swap D p z]
    linarith
  have hpAz : 0 < orientation p A z := by
    rw [orientation_swap A p z]
    linarith
  have hpAD : 0 < orientation p A D := by
    rw [orientation_cyclic' A D p]
    exact hADp
  have hplucker := hmptSeparation_orientation_plucker p q A D z
  rcases hside with ⟨hA, hD⟩ | ⟨hA, hD⟩
  · exact Or.inl ⟨hA, by nlinarith⟩
  · exact Or.inr ⟨hA, by nlinarith⟩

private theorem SukConsecutiveRawPools.hmptSeparation_remote_base_neg
    {L : ℕ} {anchors : ℕ → Point 2}
    {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (i j : Fin L)
    (hseparated : i.val + 1 < j.val ∨ j.val + 1 < i.val)
    {z : Point 2} (hz : z ∈ pools j.val) :
    orientation (anchors (i.val + 1)) (anchors (i.val + 2)) z < 0 := by
  rcases hseparated with hij | hji
  · exact (hraw.hmptSeparation_contractedRegion j.isLt hz
      (a := i.val + 1) (b := i.val + 2)
      (c := j.val + 2) (d := j.val + 3)
      (by omega) (by omega) (by omega) (by omega) (by omega)).2.1
  · exact (hraw.hmptSeparation_contractedRegion j.isLt hz
      (a := j.val) (b := j.val + 1)
      (c := i.val + 1) (d := i.val + 2)
      (by omega) (by omega) (by omega) (by omega) (by omega)).2.2

private theorem hmptSeparation_crossed_segments_orientation_neg
    (outerLeft outerRight p q : Point 2)
    (hp : 0 < orientation outerLeft outerRight p)
    (hq : 0 < orientation outerLeft outerRight q)
    (hleft : orientation outerLeft p q ≠ 0)
    (hright : orientation outerRight p q ≠ 0)
    (hcrossed : Set.Nonempty
      (convexHull ℝ ({outerLeft, q} : Set (Point 2)) ∩
        convexHull ℝ ({outerRight, p} : Set (Point 2)))) :
    orientation outerLeft p q < 0 ∧
      orientation outerRight p q < 0 := by
  rcases hcrossed with ⟨x, hxLeft, hxRight⟩
  rw [convexHull_pair, segment_eq_image] at hxLeft hxRight
  rcases hxLeft with ⟨t, ht, htx⟩
  rcases hxRight with ⟨u, hu, hux⟩
  have hAqx : orientation outerLeft q x = 0 := by
    rw [← htx, orientation_affine_combo_right outerLeft q outerLeft q
      (1 - t) t (by ring)]
    simp
  have hAqxCombo :
      orientation outerLeft q x =
        (1 - u) * orientation outerLeft q outerRight +
          u * orientation outerLeft q p := by
    rw [← hux, orientation_affine_combo_right outerLeft q outerRight p
      (1 - u) u (by ring)]
  rw [orientation_swap_last outerLeft outerRight q,
    orientation_swap_last outerLeft p q] at hAqxCombo
  have heqLeft :
      (1 - u) * orientation outerLeft outerRight q +
        u * orientation outerLeft p q = 0 := by
    nlinarith
  have huPos : 0 < u := by
    by_contra hnot
    have huZero : u = 0 := le_antisymm (le_of_not_gt hnot) hu.1
    rw [huZero] at heqLeft
    simp at heqLeft
    linarith
  have hleftWeak : orientation outerLeft p q ≤ 0 := by
    nlinarith [hu.2]
  have hDpx : orientation outerRight p x = 0 := by
    rw [← hux, orientation_affine_combo_right outerRight p outerRight p
      (1 - u) u (by ring)]
    simp
  have hDpxCombo :
      orientation outerRight p x =
        (1 - t) * orientation outerRight p outerLeft +
          t * orientation outerRight p q := by
    rw [← htx, orientation_affine_combo_right outerRight p outerLeft q
      (1 - t) t (by ring)]
  rw [orientation_cyclic outerLeft outerRight p] at hDpxCombo
  have heqRight :
      (1 - t) * orientation outerLeft outerRight p +
        t * orientation outerRight p q = 0 := by
    nlinarith
  have htPos : 0 < t := by
    by_contra hnot
    have htZero : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1
    rw [htZero] at heqRight
    simp at heqRight
    linarith
  have hrightWeak : orientation outerRight p q ≤ 0 := by
    nlinarith [ht.2]
  exact ⟨lt_of_le_of_ne hleftWeak hleft,
    lt_of_le_of_ne hrightWeak hright⟩

private theorem hmptSeparation_horizontalLT_sameStrictSide
    {outerLeft rightAnchor leftAnchor outerRight : Point 2}
    {s : Finset (Point 2)}
    (geometry : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    {p q : Point 2} (hp : p ∈ s) (hq : q ∈ s)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p q) :
    SameStrictSide p q outerLeft outerRight := by
  let p' : ↥s := ⟨p, hp⟩
  let q' : ↥s := ⟨q, hq⟩
  have hpBase : 0 < orientation outerLeft outerRight p := by
    simpa [p'] using geometry.base_orientation_pos p'
  have hqBase : 0 < orientation outerLeft outerRight q := by
    simpa [q'] using geometry.base_orientation_pos q'
  have houterLeftP : outerLeft ≠ p := by
    intro h
    subst p
    simp at hpBase
  have houterLeftQ : outerLeft ≠ q := by
    intro h
    subst q
    simp at hqBase
  have houterRightP : outerRight ≠ p := by
    intro h
    subst p
    simp at hpBase
  have houterRightQ : outerRight ≠ q := by
    intro h
    subst q
    simp at hqBase
  have hleft : orientation outerLeft p q ≠ 0 :=
    geometry.generalPosition (by simp) (by simp [hp]) (by simp [hq])
      houterLeftP houterLeftQ hpq.1
  have hright : orientation outerRight p q ≠ 0 :=
    geometry.generalPosition (by simp) (by simp [hp]) (by simp [hq])
      houterRightP houterRightQ hpq.1
  have hsigns := hmptSeparation_crossed_segments_orientation_neg
    outerLeft outerRight p q hpBase hqBase hleft hright hpq.2
  apply Or.inl
  constructor
  · rw [orientation_cyclic outerLeft p q]
    exact hsigns.1
  · rw [orientation_cyclic outerRight p q]
    exact hsigns.2

private theorem hmptSeparation_sameStrictSide_reverse_line
    {a b c d : Point 2} (h : SameStrictSide b a c d) :
    SameStrictSide a b c d := by
  rcases h with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · apply Or.inr
    constructor
    · rw [orientation_swap a b c] at hc
      linarith
    · rw [orientation_swap a b d] at hd
      linarith
  · apply Or.inl
    constructor
    · rw [orientation_swap a b c] at hc
      linarith
    · rw [orientation_swap a b d] at hd
      linarith

namespace PorValtrSupportProductData

/-- Same-parity distinct cyclic pools have a common linear rotation in
which their indices are nonadjacent.  The second disjunct of the proof uses
the reverse rotation for cyclic distance `2 * r - 2`. -/
theorem exists_cyclicParitySeparationPlacement
    {P : Finset (Point 2)} {r : ℕ}
    (_h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (_hgp : InGeneralPosition P)
    (i j : Fin (2 * r))
    (hparity : i.val % 2 = j.val % 2) (hij : i ≠ j) :
    ∃ start : Fin (2 * r), ∃ a b : Fin (2 * r - 3),
      (start.val + a.val) % (2 * r) = i.val ∧
        (start.val + b.val) % (2 * r) = j.val ∧
          (a.val + 1 < b.val ∨ b.val + 1 < a.val) := by
  have hijVal : i.val ≠ j.val := by
    intro hval
    exact hij (Fin.ext hval)
  by_cases hlt : i.val < j.val
  · have hgap : 2 ≤ j.val - i.val := by omega
    by_cases hsmall : j.val - i.val < 2 * r - 3
    · refine ⟨i, ⟨0, by omega⟩, ⟨j.val - i.val, hsmall⟩, ?_, ?_, ?_⟩
      · simp [Nat.mod_eq_of_lt i.isLt]
      · rw [show i.val + (j.val - i.val) = j.val by omega,
          Nat.mod_eq_of_lt j.isLt]
      · left
        simpa using hgap
    · have hgapEq : j.val - i.val = 2 * r - 2 := by omega
      have hjWrap : j.val + 2 = i.val + 2 * r := by omega
      refine ⟨j, ⟨2, by omega⟩, ⟨0, by omega⟩, ?_, ?_, ?_⟩
      · rw [hjWrap, Nat.add_mod, Nat.mod_self, add_zero,
          Nat.mod_mod]
        exact Nat.mod_eq_of_lt i.isLt
      · simp [Nat.mod_eq_of_lt j.isLt]
      · right
        norm_num
  · have hjlt : j.val < i.val := by omega
    have hgap : 2 ≤ i.val - j.val := by omega
    by_cases hsmall : i.val - j.val < 2 * r - 3
    · refine ⟨j, ⟨i.val - j.val, hsmall⟩, ⟨0, by omega⟩, ?_, ?_, ?_⟩
      · rw [show j.val + (i.val - j.val) = i.val by omega,
          Nat.mod_eq_of_lt i.isLt]
      · simp [Nat.mod_eq_of_lt j.isLt]
      · right
        simpa using hgap
    · have hgapEq : i.val - j.val = 2 * r - 2 := by omega
      have hiWrap : i.val + 2 = j.val + 2 * r := by omega
      refine ⟨i, ⟨0, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩
      · simp [Nat.mod_eq_of_lt i.isLt]
      · rw [hiWrap, Nat.add_mod, Nat.mod_self, add_zero,
          Nat.mod_mod]
        exact Nat.mod_eq_of_lt j.isLt
      · left
        norm_num

/-- A strict horizontal comparison in one pool propagates its supporting line
to every point of a distinct same-parity pool. -/
theorem horizontalPair_remote_sameStrictSide
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (hgp : InGeneralPosition P)
    (i j : Fin (2 * r))
    (hparity : i.val % 2 = j.val % 2) (hij : i ≠ j)
    {p q z : Point 2}
    (hp : p ∈ h.hmptPool i) (hq : q ∈ h.hmptPool i)
    (hz : z ∈ h.hmptPool j)
    (hcompare :
      HMPTSpikeHorizontalLT (h.hmptAnchor i 0) (h.hmptAnchor i 3) p q ∨
        HMPTSpikeHorizontalLT (h.hmptAnchor i 0) (h.hmptAnchor i 3) q p) :
    SameStrictSide p q (h.hmptAnchor i 0) z := by
  obtain ⟨start, a, b, ha, hb, hseparated⟩ :=
    h.exists_cyclicParitySeparationPlacement hr hgp i j hparity hij
  let raw := hmptSeparation_window h hr hgp start
  have hpRaw : p ∈ hmptSeparationPool h hr start a.val := by
    rw [hmptSeparationPool_eq h hr start a.val i ha]
    exact hp
  have hqRaw : q ∈ hmptSeparationPool h hr start a.val := by
    rw [hmptSeparationPool_eq h hr start a.val i ha]
    exact hq
  have hzRaw : z ∈ hmptSeparationPool h hr start b.val := by
    rw [hmptSeparationPool_eq h hr start b.val j hb]
    exact hz
  have hlocal := (h.toHMPTCyclicSpikeGeometry hr hgp).localRegion i
  have hside : SameStrictSide p q
      (h.hmptAnchor i 0) (h.hmptAnchor i 3) := by
    rcases hcompare with hpq | hqp
    · exact hmptSeparation_horizontalLT_sameStrictSide hlocal hp hq hpq
    · exact hmptSeparation_sameStrictSide_reverse_line
        (hmptSeparation_horizontalLT_sameStrictSide hlocal hq hp hqp)
  have hanchorZero := hmptSeparationAnchor_eq h hr start a.val i ha (0 : Fin 5)
  have hanchorThree := hmptSeparationAnchor_eq h hr start a.val i ha (3 : Fin 5)
  have hanchorZero' : hmptSeparationAnchor h hr start a.val =
      h.hmptAnchor i 0 := by
    simpa using hanchorZero
  have hanchorThree' : hmptSeparationAnchor h hr start (a.val + 3) =
      h.hmptAnchor i 3 := by
    simpa using hanchorThree
  have hsideRaw : SameStrictSide p q
      (hmptSeparationAnchor h hr start a.val)
      (hmptSeparationAnchor h hr start (a.val + 3)) := by
    rw [hanchorZero', hanchorThree']
    exact hside
  have hremote := raw.hmptSeparation_remote_sameStrictSide
    a b hseparated hpRaw hqRaw hzRaw hsideRaw
  rw [hanchorZero'] at hremote
  exact hremote

/-- The local spike base edge strictly separates its pool from every distinct
same-parity pool. -/
theorem baseEdge_remote_oppositeSide
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (hgp : InGeneralPosition P)
    (i j : Fin (2 * r))
    (hparity : i.val % 2 = j.val % 2) (hij : i ≠ j)
    {p z : Point 2}
    (hp : p ∈ h.hmptPool i) (hz : z ∈ h.hmptPool j) :
    orientation (h.hmptAnchor i 1) (h.hmptAnchor i 2) p *
      orientation (h.hmptAnchor i 1) (h.hmptAnchor i 2) z < 0 := by
  obtain ⟨start, a, b, ha, hb, hseparated⟩ :=
    h.exists_cyclicParitySeparationPlacement hr hgp i j hparity hij
  let raw := hmptSeparation_window h hr hgp start
  have hzRaw : z ∈ hmptSeparationPool h hr start b.val := by
    rw [hmptSeparationPool_eq h hr start b.val j hb]
    exact hz
  have hpPos : 0 <
      orientation (h.hmptAnchor i 1) (h.hmptAnchor i 2) p :=
    ((h.toHMPTCyclicSpikeGeometry hr hgp).localRegion i).region hp |>.1
  have hzNegRaw := raw.hmptSeparation_remote_base_neg a b hseparated hzRaw
  have hanchorOne := hmptSeparationAnchor_eq h hr start a.val i ha (1 : Fin 5)
  have hanchorTwo := hmptSeparationAnchor_eq h hr start a.val i ha (2 : Fin 5)
  have hzNeg : orientation
      (h.hmptAnchor i 1) (h.hmptAnchor i 2) z < 0 := by
    rw [← hanchorOne, ← hanchorTwo]
    exact hzNegRaw
  exact mul_neg_of_pos_of_neg hpPos hzNeg

end PorValtrSupportProductData

end

end ErdosSzekeres

end
