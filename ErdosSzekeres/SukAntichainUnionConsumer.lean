module

public import ErdosSzekeres.SukConsecutiveDilworth
public import ErdosSzekeres.SukAntichainBaseSeparation
public import ErdosSzekeres.SukCyclicSupportContraction
public import ErdosSzekeres.CupCap
public import ErdosSzekeres.TothValtrOrderType

@[expose] public section

/-!
# The nonadjacent-antichain branch of Suk's global split

This module extracts an ordinary cup or a base-supported cap from each actual
raw-pool antichain.  Nonadjacency then propagates every local supporting line
to the other selected pools, so the internally produced caps have a convex,
cardinality-exact union.
-/

namespace ErdosSzekeres

noncomputable section

/-- A cap in one antichain pool, with the exact base-side support needed to
propagate each of its vertex supports to the other nonadjacent pools. -/
def SukRegionBaseSupportedCap
    (baseLeft baseRight : Point 2)
    (cap : Finset (Point 2)) : Prop :=
  2 ≤ cap.card ∧
    ∀ ⦃p : Point 2⦄, p ∈ cap →
      ∃ q ∈ cap, p ≠ q ∧
        SameStrictSide p q baseLeft baseRight ∧
          ∀ ⦃z : Point 2⦄, z ∈ cap → z ≠ p → z ≠ q →
            SameStrictSide p q baseLeft z

private theorem sukAntichain_orientation_plucker (a b c d e : Point 2) :
    orientation a b c * orientation a d e -
      orientation a b d * orientation a c e +
      orientation a b e * orientation a c d = 0 := by
  simp only [orientation]
  ring

private theorem sukAntichain_support_base_orientation_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (habd : orientation a b d < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (habp : orientation a b p < 0)
    (hcdp : orientation c d p < 0) :
    0 < orientation a d p := by
  have hpluckerC := sukAntichain_orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p, orientation_swap b c d] at hpluckerC
  have hcap : orientation c a p < 0 := by
    nlinarith
  have hacp : 0 < orientation a c p := by
    rw [orientation_swap a c p] at hcap
    linarith
  have hpluckerA := sukAntichain_orientation_plucker a b c d p
  nlinarith

private theorem sukAntichain_support_left_diagonal_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (hcdp : orientation c d p < 0) :
    0 < orientation a c p := by
  have hplucker := sukAntichain_orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

private theorem sukAntichain_support_left_diagonal_neg
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : orientation b c p < 0)
    (hcdp : 0 < orientation c d p) :
    orientation a c p < 0 := by
  have hplucker := sukAntichain_orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

/- The earlier two-wedge transport proof is retained as design history only;
the compiled remote bridge below uses the shorter audited Plücker derivation.

private theorem sukAntichain_orientation_reverse (a b c : Point 2) :
    orientation c b a = -orientation a b c := by
  simp only [orientation]
  ring

/-- The wedge calculation from two consecutive support cells, stated without
the chain hypothesis used by the adjacent-chain consumer. -/
private theorem sukAntichain_left_wedge
    (x0 x1 x2 x3 x4 p z : Point 2)
    (h012 : orientation x0 x1 x2 < 0)
    (h013 : orientation x0 x1 x3 < 0)
    (h023 : orientation x0 x2 x3 < 0)
    (h034 : orientation x0 x3 x4 < 0)
    (h123 : orientation x1 x2 x3 < 0)
    (h234 : orientation x2 x3 x4 < 0)
    (hp : p ∈ SukSupportRegion x0 x1 x2 x3)
    (hz : z ∈ SukSupportRegion x1 x2 x3 x4) :
    (0 < orientation p x0 x2 ∧ 0 < orientation p x3 x2) ∧
      (0 < orientation p x0 z ∧ 0 < orientation p x3 z) := by
  rcases hp with ⟨h12p, h01p, h23p⟩
  rcases hz with ⟨h23z, h12z, h34z⟩
  have h02p : 0 < orientation x0 x2 p :=
    sukAntichain_support_left_diagonal_pos x0 x1 x2 x3 p
      h012 h023 h123 h12p h23p
  have h02z : orientation x0 x2 z < 0 :=
    sukAntichain_support_left_diagonal_neg x0 x1 x2 x3 z
      h012 h023 h123 h12z h23z
  have h03p : 0 < orientation x0 x3 p :=
    sukAntichain_support_base_orientation_pos x0 x1 x2 x3 p
      h012 h013 h023 h123 h12p h01p h23p
  have h03z : 0 < orientation x0 x3 z := by
    have hplucker := sukAntichain_orientation_plucker x3 x0 x2 x4 z
    rw [orientation_cyclic' x0 x2 x3,
      orientation_swap x0 x3 x4, orientation_swap x2 x3 z,
      orientation_swap x0 x3 z, orientation_swap x2 x3 x4] at hplucker
    nlinarith
  have h3pz : orientation x3 p z < 0 := by
    have hplucker := sukAntichain_orientation_plucker x3 x0 x2 p z
    rw [orientation_cyclic' x0 x2 x3,
      orientation_swap x0 x3 p, orientation_swap x2 x3 z,
      orientation_swap x0 x3 z, orientation_swap x2 x3 p] at hplucker
    nlinarith
  have h01z : orientation x0 x1 z < 0 := by
    have hplucker := sukAntichain_orientation_plucker x0 x1 x2 x3 z
    nlinarith
  have h0pz : orientation x0 p z < 0 := by
    have hplucker := sukAntichain_orientation_plucker x0 x1 x2 p z
    nlinarith
  constructor
  · constructor
    · rw [orientation_cyclic' x0 x2 p]
      exact h02p
    · rw [sukAntichain_orientation_reverse x2 x3 p]
      linarith
  · constructor
    · rw [orientation_swap x0 p z]
      linarith
    · rw [orientation_swap x3 p z]
      linarith

/-- Points lying in the same positive two-ray wedge cannot be separated by a
line through two positive-base points when the two base endpoints themselves
are not separated. -/
private theorem sameStrictSide_of_positive_wedges
    (a b p q z : Point 2)
    (hpBase : 0 < orientation a b p)
    (hqBase : 0 < orientation a b q)
    (hpaz : 0 < orientation p a z)
    (hpbz : 0 < orientation p b z)
    (hqaz : 0 < orientation q a z)
    (hqbz : 0 < orientation q b z)
    (hside : SameStrictSide p q a b)
    (hne : orientation p q z ≠ 0) :
    SameStrictSide p q a z := by
  have hpluckerP := sukAntichain_orientation_plucker p a b q z
  have hpluckerQ := sukAntichain_orientation_plucker q a b p z
  rcases hside with ⟨hpa, hpb⟩ | ⟨hpa, hpb⟩
  · left
    refine ⟨hpa, ?_⟩
    rcases lt_or_gt_of_ne hne with hzneg | hzpos
    · exact hzneg
    · rw [orientation_cyclic' a b p, orientation_swap_last p q a,
        orientation_swap_last p q b] at hpluckerP
      rw [orientation_cyclic' a b q, orientation_swap p q z,
        orientation_cyclic p q a, orientation_cyclic p q b] at hpluckerQ
      nlinarith
  · right
    refine ⟨hpa, ?_⟩
    rcases lt_or_gt_of_ne hne with hzneg | hzpos
    · rw [orientation_cyclic' a b p, orientation_swap_last p q a,
        orientation_swap_last p q b] at hpluckerP
      rw [orientation_cyclic' a b q, orientation_swap p q z,
        orientation_cyclic p q a, orientation_cyclic p q b] at hpluckerQ
      nlinarith
    · exact hzpos

private theorem sameStrictSide_of_negative_wedges
    (a b p q z : Point 2)
    (hpBase : 0 < orientation a b p)
    (hqBase : 0 < orientation a b q)
    (hpaz : orientation p a z < 0)
    (hpbz : orientation p b z < 0)
    (hqaz : orientation q a z < 0)
    (hqbz : orientation q b z < 0)
    (hside : SameStrictSide p q a b)
    (hne : orientation p q z ≠ 0) :
    SameStrictSide p q a z := by
  have hpluckerP := sukAntichain_orientation_plucker p a b q z
  have hpluckerQ := sukAntichain_orientation_plucker q a b p z
  rcases hside with ⟨hpa, hpb⟩ | ⟨hpa, hpb⟩
  · left
    refine ⟨hpa, ?_⟩
    rcases lt_or_gt_of_ne hne with hzneg | hzpos
    · exact hzneg
    · rw [orientation_cyclic' a b p, orientation_swap_last p q a,
        orientation_swap_last p q b] at hpluckerP
      rw [orientation_cyclic' a b q, orientation_swap p q z,
        orientation_cyclic p q a, orientation_cyclic p q b] at hpluckerQ
      nlinarith
  · right
    refine ⟨hpa, ?_⟩
    rcases lt_or_gt_of_ne hne with hzneg | hzpos
    · rw [orientation_cyclic' a b p, orientation_swap_last p q a,
        orientation_swap_last p q b] at hpluckerP
      rw [orientation_cyclic' a b q, orientation_swap p q z,
        orientation_cyclic p q a, orientation_cyclic p q b] at hpluckerQ
      nlinarith
    · exact hzpos

private theorem sukAntichain_right_wedge
    (x0 x1 x2 x3 x4 p z : Point 2)
    (h012 : orientation x0 x1 x2 < 0)
    (h014 : orientation x0 x1 x4 < 0)
    (h123 : orientation x1 x2 x3 < 0)
    (h124 : orientation x1 x2 x4 < 0)
    (h134 : orientation x1 x3 x4 < 0)
    (h234 : orientation x2 x3 x4 < 0)
    (hp : p ∈ SukSupportRegion x1 x2 x3 x4)
    (hz : z ∈ SukSupportRegion x0 x1 x2 x3) :
    (orientation p x1 x2 < 0 ∧ orientation p x4 x2 < 0) ∧
      (orientation p x1 z < 0 ∧ orientation p x4 z < 0) := by
  rcases hp with ⟨h23p, h12p, h34p⟩
  rcases hz with ⟨h12z, h01z, h23z⟩
  have h24p : 0 < orientation x2 x4 p := by
    have hplucker := sukAntichain_orientation_plucker x2 x1 x3 x4 p
    rw [orientation_swap x1 x2 x3, orientation_swap x1 x2 x4,
      orientation_swap x1 x2 p] at hplucker
    nlinarith
  have h24z : orientation x2 x4 z < 0 := by
    have hplucker := sukAntichain_orientation_plucker x2 x1 x3 x4 z
    rw [orientation_swap x1 x2 x3, orientation_swap x1 x2 x4,
      orientation_swap x1 x2 z] at hplucker
    nlinarith
  have h14p : 0 < orientation x1 x4 p :=
    sukAntichain_support_base_orientation_pos x1 x2 x3 x4 p
      h123 h124 h134 h234 h23p h12p h34p
  have h14z : 0 < orientation x1 x4 z := by
    have hplucker := sukAntichain_orientation_plucker x1 x0 x2 x4 z
    rw [orientation_swap x0 x1 x2, orientation_swap x0 x1 x4,
      orientation_swap x0 x1 z] at hplucker
    nlinarith
  have h1zp : orientation x1 z p < 0 := by
    have hplucker := sukAntichain_orientation_plucker x1 x2 x4 z p
    nlinarith
  have h4zp : orientation x4 z p < 0 := by
    have hplucker := sukAntichain_orientation_plucker x4 x1 x2 z p
    rw [orientation_cyclic' x1 x2 x4,
      orientation_swap x1 x4 z, orientation_swap x2 x4 p,
      orientation_swap x1 x4 p, orientation_swap x2 x4 z] at hplucker
    nlinarith
  constructor
  · constructor
    · rw [orientation_cyclic' x1 x2 p]
      exact h12p
    · rw [sukAntichain_orientation_reverse x2 x4 p]
      linarith
  · constructor
    · rw [orientation_cyclic' x1 z p]
      exact h1zp
    · rw [orientation_cyclic' x4 z p]
      exact h4zp

private theorem sameStrictSide_expand_right
    (a d e p q : Point 2)
    (hadp : 0 < orientation a d p)
    (haep : 0 < orientation a e p)
    (hdep : orientation d e p < 0)
    (hside : SameStrictSide p q a d) :
    SameStrictSide p q a e := by
  have hplucker := sukAntichain_orientation_plucker p q a d e
  rw [orientation_cyclic' a d p, orientation_cyclic' a e p,
    orientation_cyclic' d e p] at hplucker
  rcases hside with ⟨hpa, hpd⟩ | ⟨hpa, hpd⟩
  · left
    refine ⟨hpa, ?_⟩
    by_contra hnot
    have hpe : 0 ≤ orientation p q e := le_of_not_gt hnot
    nlinarith
  · right
    refine ⟨hpa, ?_⟩
    by_contra hnot
    have hpe : orientation p q e ≤ 0 := le_of_not_gt hnot
    nlinarith

-/

private theorem sameStrictSide_expand_left
    (e a d p q : Point 2)
    (hadp : 0 < orientation a d p)
    (hedp : 0 < orientation e d p)
    (heap : orientation e a p < 0)
    (hside : SameStrictSide p q a d) :
    SameStrictSide p q e d := by
  have hplucker := sukAntichain_orientation_plucker p q e a d
  rw [orientation_cyclic' a d p, orientation_cyclic' e d p,
    orientation_cyclic' e a p] at hplucker
  rcases hside with ⟨hpa, hpd⟩ | ⟨hpa, hpd⟩
  · left
    refine ⟨?_, hpd⟩
    by_contra hnot
    have hpe : 0 ≤ orientation p q e := le_of_not_gt hnot
    nlinarith
  · right
    refine ⟨?_, hpd⟩
    by_contra hnot
    have hpe : orientation p q e ≤ 0 := le_of_not_gt hnot
    nlinarith

private theorem sameStrictSide_reverse_line
    {a b c d : Point 2} (h : SameStrictSide a b c d) :
    SameStrictSide b a c d := by
  rcases h with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · right
    constructor
    · rw [orientation_swap a b c]
      linarith
    · rw [orientation_swap a b d]
      linarith
  · left
    constructor
    · rw [orientation_swap a b c]
      linarith
    · rw [orientation_swap a b d]
      linarith

private theorem sameStrictSide_of_common
    {a b common c d : Point 2}
    (hc : SameStrictSide a b common c)
    (hd : SameStrictSide a b common d) :
    SameStrictSide a b c d := by
  rcases hc with ⟨hCommon, hc⟩ | ⟨hCommon, hc⟩ <;>
    rcases hd with ⟨hCommon', hd⟩ | ⟨hCommon', hd⟩
  · exact Or.inl ⟨hc, hd⟩
  · linarith
  · linarith
  · exact Or.inr ⟨hc, hd⟩

/-- The canonical projective chart used simultaneously on all raw pools. -/
private def sukAntichainChart
    (outerLeft rightAnchor outerRight p : Point 2) : Point 2 :=
  ![orientation outerLeft p rightAnchor /
      orientation outerLeft outerRight p,
    -orientation outerLeft outerRight rightAnchor /
      orientation outerLeft outerRight p]

private def sukAntichainXi
    (outerLeft rightAnchor outerRight p : Point 2) : ℝ :=
  (sukAntichainChart outerLeft rightAnchor outerRight p) 0

private theorem sukAntichainChart_orientation
    (outerLeft rightAnchor outerRight p q r : Point 2)
    (hp : orientation outerLeft outerRight p ≠ 0)
    (hq : orientation outerLeft outerRight q ≠ 0)
    (hr : orientation outerLeft outerRight r ≠ 0) :
    orientation
        (sukAntichainChart outerLeft rightAnchor outerRight p)
        (sukAntichainChart outerLeft rightAnchor outerRight q)
        (sukAntichainChart outerLeft rightAnchor outerRight r) =
      orientation outerLeft outerRight rightAnchor ^ 2 /
          (orientation outerLeft outerRight p *
            orientation outerLeft outerRight q *
            orientation outerLeft outerRight r) *
        orientation p q r := by
  change
    (orientation outerLeft q rightAnchor /
          orientation outerLeft outerRight q -
        orientation outerLeft p rightAnchor /
          orientation outerLeft outerRight p) *
        (-orientation outerLeft outerRight rightAnchor /
            orientation outerLeft outerRight r -
          -orientation outerLeft outerRight rightAnchor /
            orientation outerLeft outerRight p) -
      (-orientation outerLeft outerRight rightAnchor /
            orientation outerLeft outerRight q -
          -orientation outerLeft outerRight rightAnchor /
            orientation outerLeft outerRight p) *
        (orientation outerLeft r rightAnchor /
            orientation outerLeft outerRight r -
          orientation outerLeft p rightAnchor /
            orientation outerLeft outerRight p) = _
  field_simp
  simp only [orientation]
  ring

private theorem sukAntichainXi_difference
    (outerLeft rightAnchor outerRight p q : Point 2)
    (hp : orientation outerLeft outerRight p ≠ 0)
    (hq : orientation outerLeft outerRight q ≠ 0) :
    sukAntichainXi outerLeft rightAnchor outerRight q -
        sukAntichainXi outerLeft rightAnchor outerRight p =
      orientation outerLeft outerRight rightAnchor *
          orientation p outerLeft q /
        (orientation outerLeft outerRight p *
          orientation outerLeft outerRight q) := by
  simp only [sukAntichainXi, sukAntichainChart, Matrix.cons_val_zero]
  field_simp
  simp only [orientation]
  ring

private theorem orientation_transitive_of_first_lt_pos
    (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (habc : 0 < orientation a b c)
    (hbcd : 0 < orientation b c d) :
    0 < orientation a b d ∧ 0 < orientation a c d := by
  have habX : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hbcX : 0 < c 0 - b 0 := sub_pos.mpr hbc
  have hcdX : 0 < d 0 - c 0 := sub_pos.mpr hcd
  let uv := (b 0 - a 0) * (c 1 - b 1) -
    (b 1 - a 1) * (c 0 - b 0)
  let vw := (c 0 - b 0) * (d 1 - c 1) -
    (c 1 - b 1) * (d 0 - c 0)
  let uw := (b 0 - a 0) * (d 1 - c 1) -
    (b 1 - a 1) * (d 0 - c 0)
  have huv : 0 < uv := by
    rw [show uv = orientation a b c by
      simp only [uv, orientation]
      ring]
    exact habc
  have hvw : 0 < vw := by
    rw [show vw = orientation b c d by
      simp only [vw, orientation]
      ring]
    exact hbcd
  have hidentity : (c 0 - b 0) * uw =
      (b 0 - a 0) * vw + (d 0 - c 0) * uv := by
    simp only [uv, vw, uw]
    ring
  have hprod : 0 < (c 0 - b 0) * uw := by
    rw [hidentity]
    exact add_pos (mul_pos habX hvw) (mul_pos hcdX huv)
  have huw : 0 < uw := (mul_pos_iff_of_pos_left hbcX).mp hprod
  constructor
  · rw [show orientation a b d = uv + uw by
      simp only [orientation, uv, uw]
      ring]
    linarith
  · rw [show orientation a c d = uw + vw by
      simp only [orientation, uw, vw]
      ring]
    linarith

private theorem orientation_transitive_of_first_lt_neg
    (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (habc : orientation a b c < 0)
    (hbcd : orientation b c d < 0) :
    orientation a b d < 0 ∧ orientation a c d < 0 := by
  have habX : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hbcX : 0 < c 0 - b 0 := sub_pos.mpr hbc
  have hcdX : 0 < d 0 - c 0 := sub_pos.mpr hcd
  let uv := (b 0 - a 0) * (c 1 - b 1) -
    (b 1 - a 1) * (c 0 - b 0)
  let vw := (c 0 - b 0) * (d 1 - c 1) -
    (c 1 - b 1) * (d 0 - c 0)
  let uw := (b 0 - a 0) * (d 1 - c 1) -
    (b 1 - a 1) * (d 0 - c 0)
  have huv : uv < 0 := by
    rw [show uv = orientation a b c by
      simp only [uv, orientation]
      ring]
    exact habc
  have hvw : vw < 0 := by
    rw [show vw = orientation b c d by
      simp only [vw, orientation]
      ring]
    exact hbcd
  have hidentity : (c 0 - b 0) * uw =
      (b 0 - a 0) * vw + (d 0 - c 0) * uv := by
    simp only [uv, vw, uw]
    ring
  have hprod : (c 0 - b 0) * uw < 0 := by
    rw [hidentity]
    exact add_neg (mul_neg_of_pos_of_neg habX hvw)
      (mul_neg_of_pos_of_neg hcdX huv)
  have huw : uw < 0 := by
    by_contra hnot
    have := mul_nonneg hbcX.le (le_of_not_gt hnot)
    linarith
  constructor
  · rw [show orientation a b d = uv + uw by
      simp only [orientation, uv, uw]
      ring]
    linarith
  · rw [show orientation a c d = uw + vw by
      simp only [orientation, uw, vw]
      ring]
    linarith

private theorem SukConsecutiveRawPools.anchor_mem_carrier
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (_hraw : SukConsecutiveRawPools L anchors pools)
    {i : ℕ} (hi : i < L + 3) :
    anchors i ∈
      (Finset.range (L + 3)).image anchors ∪
        (Finset.range L).biUnion pools := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

private theorem SukConsecutiveRawPools.pool_mem_carrier
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (_hraw : SukConsecutiveRawPools L anchors pools)
    {i : ℕ} (hi : i < L) {p : Point 2} (hp : p ∈ pools i) :
    p ∈ (Finset.range (L + 3)).image anchors ∪
      (Finset.range L).biUnion pools := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hp⟩

private theorem SukConsecutiveRawPools.contractedRegion
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {i a b c d : ℕ} (hi : i < L) {p : Point 2} (hp : p ∈ pools i)
    (hab : a < b) (hbi : b ≤ i + 1) (hic : i + 2 ≤ c)
    (hcd : c < d) (hd : d < L + 3) :
    p ∈ SukSupportRegion
      (anchors a) (anchors b) (anchors c) (anchors d) := by
  apply sukSupportRegion_subset_of_strictCapBlock
    (L + 3) a b c d i anchors hraw.strictCap hab hbi hic hcd hd
  exact hraw.region i hi hp

private theorem SukConsecutiveRawPools.contracted_base_orientation_pos
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {i a b c d : ℕ} (hi : i < L) {p : Point 2} (hp : p ∈ pools i)
    (hab : a < b) (hbi : b ≤ i + 1) (hic : i + 2 ≤ c)
    (hcd : c < d) (hd : d < L + 3) :
    0 < orientation (anchors a) (anchors d) p := by
  have hregion := hraw.contractedRegion hi hp hab hbi hic hcd hd
  rcases hregion with ⟨hbase, hleft, hright⟩
  exact sukAntichain_support_base_orientation_pos
    (anchors a) (anchors b) (anchors c) (anchors d) p
    (hraw.strictCap hab (by omega) (by omega))
    (hraw.strictCap hab (by omega) hd)
    (hraw.strictCap (by omega) hcd hd)
    (hraw.strictCap (by omega) hcd hd)
    hbase hleft hright

private theorem SukConsecutiveRawPools.remote_sameStrictSide
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (i j : Fin L)
    (hseparated : i.val + 1 < j.val ∨ j.val + 1 < i.val)
    {p q x : Point 2}
    (hp : p ∈ pools i.val) (_hq : q ∈ pools i.val)
    (hx : x ∈ pools j.val) (_hpq : p ≠ q)
    (hside : SameStrictSide p q
      (anchors i.val) (anchors (i.val + 3))) :
    SameStrictSide p q (anchors i.val) x := by
  let A := anchors i.val
  let B := anchors (i.val + 1)
  let C := anchors (i.val + 2)
  let D := anchors (i.val + 3)
  have hABC : orientation A B C < 0 := hraw.strictCap (by omega) (by omega) (by omega)
  have hABD : orientation A B D < 0 := hraw.strictCap (by omega) (by omega) (by omega)
  have hACD : orientation A C D < 0 := hraw.strictCap (by omega) (by omega) (by omega)
  have hBCD : orientation B C D < 0 := hraw.strictCap (by omega) (by omega) (by omega)
  have hpRegion := hraw.region i.val i.isLt hp
  have hACp : 0 < orientation A C p :=
    sukAntichain_support_left_diagonal_pos A B C D p
      hABC hACD hBCD hpRegion.1 hpRegion.2.2
  have hADp : 0 < orientation A D p :=
    sukAntichain_support_base_orientation_pos A B C D p
      hABC hABD hACD hBCD hpRegion.1 hpRegion.2.1 hpRegion.2.2
  have hxSigns : orientation A B x < 0 ∧ orientation A C x < 0 ∧
      orientation A D x < 0 ∧ orientation C D x < 0 := by
    rcases hseparated with hij | hji
    · refine ⟨
        (hraw.contractedRegion j.isLt hx
          (a := i.val) (b := i.val + 1) (c := j.val + 2) (d := j.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.1,
        (hraw.contractedRegion j.isLt hx
          (a := i.val) (b := i.val + 2) (c := j.val + 2) (d := j.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.1,
        (hraw.contractedRegion j.isLt hx
          (a := i.val) (b := i.val + 3) (c := j.val + 2) (d := j.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.1,
        (hraw.contractedRegion j.isLt hx
          (a := i.val + 2) (b := i.val + 3)
          (c := j.val + 2) (d := j.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.1⟩
    · refine ⟨
        (hraw.contractedRegion j.isLt hx
          (a := j.val) (b := j.val + 1) (c := i.val) (d := i.val + 1)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.2,
        (hraw.contractedRegion j.isLt hx
          (a := j.val) (b := j.val + 1) (c := i.val) (d := i.val + 2)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.2,
        (hraw.contractedRegion j.isLt hx
          (a := j.val) (b := j.val + 1) (c := i.val) (d := i.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.2,
        (hraw.contractedRegion j.isLt hx
          (a := j.val) (b := j.val + 1) (c := i.val + 2) (d := i.val + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)).2.2⟩
  have hApx : orientation A p x < 0 := by
    have hplucker := sukAntichain_orientation_plucker A B C p x
    nlinarith [hpRegion.2.1, hACp, hxSigns.1, hxSigns.2.1]
  have hDpx : 0 < orientation D p x := by
    have hDac : orientation D A C < 0 := by
      rw [orientation_cyclic' A C D]
      exact hACD
    have hDap : orientation D A p < 0 := by
      rw [orientation_cyclic' A p D, orientation_swap_last A D p]
      linarith
    have hDcx : 0 < orientation D C x := by
      rw [orientation_swap C D x]
      linarith [hxSigns.2.2.2]
    have hDax : 0 < orientation D A x := by
      rw [orientation_cyclic' A x D, orientation_swap_last A D x]
      linarith [hxSigns.2.2.1]
    have hDcp : 0 < orientation D C p := by
      rw [orientation_swap C D p]
      linarith [hpRegion.2.2]
    have hplucker := sukAntichain_orientation_plucker D A C p x
    nlinarith
  have hpDx : orientation p D x < 0 := by
    rw [orientation_swap D p x]
    linarith
  have hpAx : 0 < orientation p A x := by
    rw [orientation_swap A p x]
    linarith
  have hpAD : 0 < orientation p A D := by
    rw [orientation_cyclic' A D p]
    exact hADp
  have hplucker := sukAntichain_orientation_plucker p q A D x
  rcases hside with ⟨hA, hD⟩ | ⟨hA, hD⟩
  · exact Or.inl ⟨hA, by nlinarith⟩
  · exact Or.inr ⟨hA, by nlinarith⟩

private theorem SukConsecutiveRawPools.globalRegion
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {i : ℕ} (hi : i < L) {p : Point 2} (hp : p ∈ pools i) :
    p ∈ SukSupportRegion
      (anchors 0) (anchors (i + 1))
      (anchors (i + 2)) (anchors (L + 2)) := by
  apply sukSupportRegion_subset_of_strictCapBlock
    (L + 3) 0 (i + 1) (i + 2) (L + 2) i anchors hraw.strictCap
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact hraw.region i hi hp

private theorem SukConsecutiveRawPools.chart_anchor_pos
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (hL : 0 < L) :
    0 < orientation (anchors 0) (anchors (L + 2)) (anchors 1) := by
  rw [orientation_swap_last]
  linarith [hraw.strictCap (show 0 < 1 by omega)
    (show 1 < L + 2 by omega) (show L + 2 < L + 3 by omega)]

private theorem SukConsecutiveRawPools.anchor_denominator_pos
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {k : ℕ} (hk0 : 0 < k) (hk : k < L + 2) :
    0 < orientation (anchors 0) (anchors (L + 2)) (anchors k) := by
  rw [orientation_swap_last]
  linarith [hraw.strictCap hk0 hk (show L + 2 < L + 3 by omega)]

private theorem SukConsecutiveRawPools.pool_denominator_pos
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {i : ℕ} (hi : i < L) {p : Point 2} (hp : p ∈ pools i) :
    0 < orientation (anchors 0) (anchors (L + 2)) p := by
  have hregion := hraw.globalRegion hi hp
  rcases hregion with ⟨hbase, hleft, hright⟩
  exact sukAntichain_support_base_orientation_pos
    (anchors 0) (anchors (i + 1)) (anchors (i + 2))
    (anchors (L + 2)) p
    (hraw.strictCap (by omega) (by omega) (by omega))
    (hraw.strictCap (by omega) (by omega) (by omega))
    (hraw.strictCap (by omega) (by omega) (by omega))
    (hraw.strictCap (by omega) (by omega) (by omega))
    hbase hleft hright

private theorem SukConsecutiveRawPools.pool_xi_interval
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {i : ℕ} (hi : i < L) {p : Point 2} (hp : p ∈ pools i) :
    sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2))
        (anchors (i + 1)) <
      sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2)) p ∧
    sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2)) p <
      sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2))
        (anchors (i + 2)) := by
  have hL : 0 < L := by omega
  have hanchor := hraw.chart_anchor_pos hL
  have hpDen := hraw.pool_denominator_pos hi hp
  have hleftDen := hraw.anchor_denominator_pos (show 0 < i + 1 by omega) (by omega)
  have hrightDen := hraw.anchor_denominator_pos (show 0 < i + 2 by omega) (by omega)
  have hregion := hraw.globalRegion hi hp
  rcases hregion with ⟨hbase, hleft, hright⟩
  have hleftOrient : 0 < orientation (anchors (i + 1)) (anchors 0) p := by
    rw [orientation_swap]
    linarith
  have hrightOrient : 0 < orientation p (anchors 0) (anchors (i + 2)) := by
    rw [← orientation_cyclic p (anchors 0) (anchors (i + 2))]
    exact sukAntichain_support_left_diagonal_pos
      (anchors 0) (anchors (i + 1)) (anchors (i + 2))
      (anchors (L + 2)) p
      (hraw.strictCap (by omega) (by omega) (by omega))
      (hraw.strictCap (by omega) (by omega) (by omega))
      (hraw.strictCap (by omega) (by omega) (by omega))
      hbase hright
  constructor
  · have hdiff := sukAntichainXi_difference
      (anchors 0) (anchors 1) (anchors (L + 2))
      (anchors (i + 1)) p (ne_of_gt hleftDen) (ne_of_gt hpDen)
    rw [← sub_pos, hdiff]
    exact div_pos (mul_pos hanchor hleftOrient) (mul_pos hleftDen hpDen)
  · have hdiff := sukAntichainXi_difference
      (anchors 0) (anchors 1) (anchors (L + 2))
      p (anchors (i + 2)) (ne_of_gt hpDen) (ne_of_gt hrightDen)
    rw [← sub_pos, hdiff]
    exact div_pos (mul_pos hanchor hrightOrient) (mul_pos hpDen hrightDen)

private theorem SukConsecutiveRawPools.pool_xi_injective
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {i : ℕ} (hi : i < L) :
    Set.InjOn
      (sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2)))
      (pools i) := by
  intro p hp q hq heq
  by_contra hpq
  have hpDen := hraw.pool_denominator_pos hi hp
  have hqDen := hraw.pool_denominator_pos hi hq
  have hL : 0 < L := by omega
  have hanchor := hraw.chart_anchor_pos hL
  have hdiff := sukAntichainXi_difference
    (anchors 0) (anchors 1) (anchors (L + 2)) p q
    (ne_of_gt hpDen) (ne_of_gt hqDen)
  rw [heq, sub_self] at hdiff
  field_simp [ne_of_gt hpDen, ne_of_gt hqDen] at hdiff
  have horientation : orientation p (anchors 0) q = 0 := by
    nlinarith
  have hp0 : p ≠ anchors 0 := by
    intro h
    subst p
    simp at hpDen
  have hq0 : q ≠ anchors 0 := by
    intro h
    subst q
    simp at hqDen
  have hne : orientation p (anchors 0) q ≠ 0 :=
    hraw.generalPosition
      (hraw.pool_mem_carrier hi hp)
      (hraw.anchor_mem_carrier (show 0 < L + 3 by omega))
      (hraw.pool_mem_carrier hi hq) hp0 hpq hq0.symm
  exact hne horientation

private theorem SukConsecutiveRawPools.anchor_xi_lt
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b < L + 2) :
    sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2)) (anchors a) <
      sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2)) (anchors b) := by
  have hL : 0 < L := by omega
  have hanchor := hraw.chart_anchor_pos hL
  have haDen := hraw.anchor_denominator_pos ha (hab.trans hb)
  have hbDen := hraw.anchor_denominator_pos (ha.trans hab) hb
  have horient : 0 < orientation (anchors a) (anchors 0) (anchors b) := by
    rw [orientation_swap]
    linarith [hraw.strictCap ha hab (hb.trans (by omega))]
  have hdiff := sukAntichainXi_difference
    (anchors 0) (anchors 1) (anchors (L + 2))
    (anchors a) (anchors b) (ne_of_gt haDen) (ne_of_gt hbDen)
  rw [← sub_pos, hdiff]
  exact div_pos (mul_pos hanchor horient) (mul_pos haDen hbDen)

private theorem SukConsecutiveRawPools.ordered_pair_baseLeft_neg
    {L : ℕ} {anchors : ℕ → Point 2} {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (i : Fin L) {p q : Point 2}
    (hp : p ∈ pools i.val) (hq : q ∈ pools i.val)
    (hxi : sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2)) p <
      sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2)) q)
    (hside : SameStrictSide p q
      (anchors i.val) (anchors (i.val + 3))) :
    orientation p q (anchors i.val) < 0 := by
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hanchor := hraw.chart_anchor_pos hL
  have hpDen := hraw.pool_denominator_pos i.isLt hp
  have hqDen := hraw.pool_denominator_pos i.isLt hq
  have hdiff := sukAntichainXi_difference
    (anchors 0) (anchors 1) (anchors (L + 2)) p q
    (ne_of_gt hpDen) (ne_of_gt hqDen)
  have hquot : 0 <
      orientation (anchors 0) (anchors (L + 2)) (anchors 1) *
          orientation p (anchors 0) q /
        (orientation (anchors 0) (anchors (L + 2)) p *
          orientation (anchors 0) (anchors (L + 2)) q) := by
    rw [← hdiff]
    linarith
  have hnum : 0 <
      orientation (anchors 0) (anchors (L + 2)) (anchors 1) *
        orientation p (anchors 0) q := by
    rcases (div_pos_iff.mp hquot) with h | h
    · exact h.1
    · nlinarith [mul_pos hpDen hqDen]
  have hp0q : 0 < orientation p (anchors 0) q := by
    nlinarith
  have hpq0 : orientation p q (anchors 0) < 0 := by
    rw [orientation_swap_last p (anchors 0) q]
    linarith
  by_cases hi0 : i.val = 0
  · simpa [hi0] using hpq0
  · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi0
    have hpLocal : 0 < orientation (anchors i.val) (anchors (i.val + 3)) p :=
      hraw.contracted_base_orientation_pos i.isLt hp
        (a := i.val) (b := i.val + 1) (c := i.val + 2) (d := i.val + 3)
        (by omega) (by omega) (by omega) (by omega) (by omega)
    have hpWide : 0 < orientation (anchors 0) (anchors (i.val + 3)) p :=
      hraw.contracted_base_orientation_pos i.isLt hp
        (a := 0) (b := i.val) (c := i.val + 2) (d := i.val + 3)
        hiPos (by omega) (by omega) (by omega) (by omega)
    have hpBetween : orientation (anchors 0) (anchors i.val) p < 0 := by
      exact (hraw.contractedRegion i.isLt hp
        (a := 0) (b := i.val) (c := i.val + 2) (d := i.val + 3)
        hiPos (by omega) (by omega) (by omega) (by omega)).2.1
    have hwide : SameStrictSide p q (anchors 0) (anchors (i.val + 3)) :=
      sameStrictSide_expand_left
        (anchors 0) (anchors i.val) (anchors (i.val + 3)) p q
        hpLocal hpWide hpBetween hside
    rcases hwide with ⟨hzero, hright⟩ | ⟨hzero, hright⟩
    · rcases hside with ⟨hleft, -⟩ | ⟨-, hrightPos⟩
      · exact hleft
      · linarith
    · linarith

private structure SukAntichainOrderedPoint (s : Finset (Point 2)) where
  val : ↥s
  deriving Fintype

private def sukAntichainOrderedPointEquiv (s : Finset (Point 2)) :
    SukAntichainOrderedPoint s ≃ ↥s where
  toFun p := p.val
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl

private def sukAntichainSelected
    {s : Finset (Point 2)} (e : Fin s.card ≃ ↥s)
    {k : ℕ} (f : Fin k ↪o Fin s.card) : Finset (Point 2) :=
  Finset.univ.image fun u => (e (f u)).1

private theorem sukAntichainSelected_subset
    {s : Finset (Point 2)} (e : Fin s.card ≃ ↥s)
    {k : ℕ} (f : Fin k ↪o Fin s.card) :
    sukAntichainSelected e f ⊆ s := by
  intro p hp
  simp only [sukAntichainSelected, Finset.mem_image, Finset.mem_univ,
    true_and] at hp
  obtain ⟨u, rfl⟩ := hp
  exact (e (f u)).property

private theorem sukAntichainSelected_card
    {s : Finset (Point 2)} (e : Fin s.card ≃ ↥s)
    {k : ℕ} (f : Fin k ↪o Fin s.card) :
    (sukAntichainSelected e f).card = k := by
  have hinjective : Function.Injective (fun u => (e (f u)).1) := by
    intro u v huv
    apply f.injective
    apply e.injective
    exact Subtype.ext huv
  rw [sukAntichainSelected, Finset.card_image_of_injective _ hinjective]
  simp

private theorem sukAntichain_restrict_pointFinset
    {s : Finset (Point 2)} (e : Fin s.card ≃ ↥s)
    (F : Point 2 → Point 2)
    (C : SweptConfiguration s.card)
    (hpoint : ∀ u, C.point u = F (e u).1)
    {k : ℕ} (f : Fin k ↪o Fin s.card) :
    (C.restrict f).pointFinset = (sukAntichainSelected e f).image F := by
  rw [SweptConfiguration.pointFinset, sukAntichainSelected, Finset.image_image]
  apply Finset.image_congr
  intro u _
  simp only [SweptConfiguration.restrict_point, Function.comp_apply]
  exact hpoint (f u)

private theorem sukAntichainSelected_inConvexPosition
    {s : Finset (Point 2)}
    (hgp : InGeneralPosition s)
    (F : Point 2 → Point 2)
    (hinj : Set.InjOn F s)
    (hsign : PreservesOrientationSignsOn F s)
    (e : Fin s.card ≃ ↥s)
    (C : SweptConfiguration s.card)
    (hpoint : ∀ u, C.point u = F (e u).1)
    {k : ℕ} (f : Fin k ↪o Fin s.card)
    (hmono : IsMonochromaticChain C.tripleColoring c f) :
    InConvexPosition (sukAntichainSelected e f) := by
  have hchart : InConvexPosition (C.restrict f).pointFinset := by
    apply (C.restrict f).inConvexPosition_pointFinset_iff_isStrongPolygon.mpr
    exact CupCap.IsMonochromaticChain.isStrongPolygonOn hmono
  rw [sukAntichain_restrict_pointFinset e F C hpoint f] at hchart
  have hselectedSubset := sukAntichainSelected_subset e f
  exact (inConvexPosition_image_iff_of_preservesOrientationSignsOn
    (hgp.mono hselectedSubset)
    (fun _ ha _ hb ↦ hinj (hselectedSubset ha) (hselectedSubset hb))
    (fun _ ha _ hb _ hc ↦
      hsign (hselectedSubset ha) (hselectedSubset hb) (hselectedSubset hc))).mp hchart

private theorem sukAntichain_orientation_finset_affine
    (p q : Point 2) (t : Finset (Point 2)) (w : Point 2 → ℝ)
    (hw : ∑ z ∈ t, w z = 1) :
    orientation p q (∑ z ∈ t, w z • z) =
      ∑ z ∈ t, w z * orientation p q z := by
  let linearPart : Point 2 → ℝ := fun z ↦
    (q 0 - p 0) * z 1 - (q 1 - p 1) * z 0
  have horient (z : Point 2) :
      orientation p q z = linearPart z - linearPart p := by
    simp only [orientation, linearPart]
    ring
  rw [horient]
  have hlinear :
      linearPart (∑ z ∈ t, w z • z) =
        ∑ z ∈ t, w z * linearPart z := by
    simp only [linearPart, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hlinear]
  simp_rw [horient, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hw, one_mul]

private theorem inConvexPosition_of_strict_vertex_support
    {s : Finset (Point 2)}
    (hsupport : ∀ ⦃p : Point 2⦄, p ∈ s →
      ∃ q ∈ s, ∃ common : Point 2,
        p ≠ q ∧ orientation p q common ≠ 0 ∧
        ∀ ⦃z : Point 2⦄, z ∈ s → z ≠ p → z ≠ q →
          SameStrictSide p q common z) :
    InConvexPosition s := by
  classical
  intro p hp hphull
  obtain ⟨q, hq, common, hpq, hcommonNe, hall⟩ := hsupport hp
  have hqErase : q ∈ s.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  obtain ⟨w, hwNonneg, hwSum, hwPoint⟩ :=
    Finset.mem_convexHull'.mp hphull
  have haffine := sukAntichain_orientation_finset_affine
    p q (s.erase p) w hwSum
  rw [hwPoint, orientation_first_eq_third] at haffine
  have finish
      (hweightZero : ∀ z ∈ s.erase p, z ≠ q → w z = 0) : False := by
    have hsumSingle : ∑ z ∈ s.erase p, w z = w q := by
      apply Finset.sum_eq_single q
      · intro z hz hzq
        exact hweightZero z hz hzq
      · simp [hqErase]
    have hwq : w q = 1 := by
      rw [← hsumSingle]
      exact hwSum
    have hpointSingle : ∑ z ∈ s.erase p, w z • z = w q • q := by
      apply Finset.sum_eq_single q
      · intro z hz hzq
        rw [hweightZero z hz hzq, zero_smul]
      · simp [hqErase]
    rw [hpointSingle, hwq, one_smul] at hwPoint
    exact hpq hwPoint.symm
  rcases lt_or_gt_of_ne hcommonNe with hcommonNeg | hcommonPos
  · have hterm : ∀ z ∈ s.erase p,
        w z * orientation p q z ≤ 0 := by
      intro z hz
      by_cases hzq : z = q
      · subst z
        simp
      · have hzSide := hall (Finset.mem_of_mem_erase hz)
          (Finset.ne_of_mem_erase hz) hzq
        have hzNeg : orientation p q z < 0 := by
          rcases hzSide with ⟨-, hzNeg⟩ | ⟨hcommonPos', -⟩
          · exact hzNeg
          · linarith
        exact mul_nonpos_of_nonneg_of_nonpos (hwNonneg z hz) hzNeg.le
    have hsumZero : ∑ z ∈ s.erase p, w z * orientation p q z = 0 :=
      haffine.symm
    have hzero := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hsumZero
    apply finish
    intro z hz hzq
    have hzSide := hall (Finset.mem_of_mem_erase hz)
      (Finset.ne_of_mem_erase hz) hzq
    have hzNeg : orientation p q z < 0 := by
      rcases hzSide with ⟨-, hzNeg⟩ | ⟨hcommonPos', -⟩
      · exact hzNeg
      · linarith
    rcases mul_eq_zero.mp (hzero z hz) with hwz | hz0
    · exact hwz
    · exact (ne_of_lt hzNeg hz0).elim
  · have hterm : ∀ z ∈ s.erase p,
        0 ≤ w z * orientation p q z := by
      intro z hz
      by_cases hzq : z = q
      · subst z
        simp
      · have hzSide := hall (Finset.mem_of_mem_erase hz)
          (Finset.ne_of_mem_erase hz) hzq
        have hzPos : 0 < orientation p q z := by
          rcases hzSide with ⟨hcommonNeg', -⟩ | ⟨-, hzPos⟩
          · linarith
          · exact hzPos
        exact mul_nonneg (hwNonneg z hz) hzPos.le
    have hsumZero : ∑ z ∈ s.erase p, w z * orientation p q z = 0 :=
      haffine.symm
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsumZero
    apply finish
    intro z hz hzq
    have hzSide := hall (Finset.mem_of_mem_erase hz)
      (Finset.ne_of_mem_erase hz) hzq
    have hzPos : 0 < orientation p q z := by
      rcases hzSide with ⟨hcommonNeg', -⟩ | ⟨-, hzPos⟩
      · linarith
      · exact hzPos
    rcases mul_eq_zero.mp (hzero z hz) with hwz | hz0
    · exact hwz
    · exact (ne_of_gt hzPos hz0).elim

theorem SukConsecutiveRawPools.antichainSubset_cup_or_baseSupportedCap
    {L n antiSize capSize : ℕ}
    {anchors : ℕ → Point 2}
    {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (i : Fin L)
    (hanti : SukRegionHasAntichainSubset
      (anchors i.val) (anchors (i.val + 3))
      (pools i.val) antiSize)
    (hn : 2 ≤ n)
    (hcapSize : 2 ≤ capSize)
    (hthreshold :
      Nat.choose (n + capSize - 4) (n - 2) < antiSize) :
    ContainsConvexSubset (pools i.val) n ∨
      ∃ cap : Finset (Point 2),
        cap ⊆ pools i.val ∧
          cap.card = capSize ∧
            SukRegionBaseSupportedCap
              (anchors i.val) (anchors (i.val + 3)) cap := by
  classical
  obtain ⟨w, hwCard, hwAnti⟩ := hanti
  let s : Finset (Point 2) := w.image fun p ↦ p.1
  have hsSubset : s ⊆ pools i.val := by
    intro p hp
    simp only [s, Finset.mem_image] at hp
    obtain ⟨p', -, rfl⟩ := hp
    exact p'.property
  have hsCard : s.card = w.card := by
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hsLarge : antiSize ≤ s.card := by
    rw [hsCard]
    exact hwCard
  have hsAnti : SukRegionPairwiseAntichain
      (anchors i.val) (anchors (i.val + 3)) s := by
    intro p hp q hq hpq
    simp only [s, Finset.mem_image] at hp hq
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    have hpq' : p' ≠ q' := by
      intro h
      apply hpq
      exact congrArg Subtype.val h
    exact ⟨fun hpqLE ↦ hwAnti hp' hq' hpq' hpqLE,
      fun hqpLE ↦ hwAnti hq' hp' hpq'.symm hqpLE⟩
  have hsSide : ∀ p ∈ s,
      0 < orientation (anchors i.val) (anchors (i.val + 3)) p := by
    intro p hp
    exact hraw.contracted_base_orientation_pos i.isLt (hsSubset hp)
      (a := i.val) (b := i.val + 1) (c := i.val + 2) (d := i.val + 3)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hsGp : InGeneralPosition s := by
    apply hraw.generalPosition.mono
    intro p hp
    exact hraw.pool_mem_carrier i.isLt (hsSubset hp)
  have hsBaseGp : InGeneralPosition
      (insert (anchors i.val) (insert (anchors (i.val + 3)) s)) := by
    apply hraw.generalPosition.mono
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · exact hraw.anchor_mem_carrier (by omega)
    · exact hraw.anchor_mem_carrier (by omega)
    · exact hraw.pool_mem_carrier i.isLt (hsSubset hp)
  let xi : Point 2 → ℝ :=
    sukAntichainXi (anchors 0) (anchors 1) (anchors (L + 2))
  have hxiInj : Set.InjOn xi s := by
    intro p hp q hq hpqXi
    exact hraw.pool_xi_injective i.isLt (hsSubset hp) (hsSubset hq) hpqXi
  letI : LinearOrder (SukAntichainOrderedPoint s) := LinearOrder.lift'
      (fun p : SukAntichainOrderedPoint s ↦ xi p.val.1) <| by
    intro p q hpqXi
    have hpq : p.val = q.val :=
      Subtype.ext (hxiInj p.val.property q.val.property hpqXi)
    cases p
    cases q
    simp_all
  have hsFintypeCard : Fintype.card (SukAntichainOrderedPoint s) = s.card := by
    rw [Fintype.card_congr (sukAntichainOrderedPointEquiv s)]
    simp
  let eOrder :=
    Fintype.orderIsoFinOfCardEq
      (SukAntichainOrderedPoint s) (k := s.card) hsFintypeCard
  let e : Fin s.card ≃ ↥s :=
    eOrder.toEquiv.trans (sukAntichainOrderedPointEquiv s)
  let F : Point 2 → Point 2 :=
    sukAntichainChart (anchors 0) (anchors 1) (anchors (L + 2))
  have hFpoint (u : Fin s.card) :
      F (e u).1 0 = xi (e u).1 := rfl
  have hFStrict : StrictMono (fun u : Fin s.card ↦ F (e u).1 0) := by
    intro u v huv
    change F (e u).1 0 < F (e v).1 0
    rw [hFpoint u, hFpoint v]
    have hsub := eOrder.strictMono huv
    change xi (eOrder u).val.1 < xi (eOrder v).val.1 at hsub
    simpa [e] using hsub
  have hFInj : Set.InjOn F s := by
    intro p hp q hq hpqF
    apply hxiInj hp hq
    exact congrFun hpqF 0
  have hFSigns : PreservesOrientationSignsOn F s := by
    intro a ha b hb c hc
    have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hanchor := hraw.chart_anchor_pos hL
    have haDen := hraw.pool_denominator_pos i.isLt (hsSubset ha)
    have hbDen := hraw.pool_denominator_pos i.isLt (hsSubset hb)
    have hcDen := hraw.pool_denominator_pos i.isLt (hsSubset hc)
    have heq := sukAntichainChart_orientation
      (anchors 0) (anchors 1) (anchors (L + 2)) a b c
      (ne_of_gt haDen) (ne_of_gt hbDen) (ne_of_gt hcDen)
    have hfactor : 0 <
        orientation (anchors 0) (anchors (L + 2)) (anchors 1) ^ 2 /
          (orientation (anchors 0) (anchors (L + 2)) a *
            orientation (anchors 0) (anchors (L + 2)) b *
            orientation (anchors 0) (anchors (L + 2)) c) :=
      div_pos (sq_pos_of_pos hanchor) (mul_pos (mul_pos haDen hbDen) hcDen)
    change
      (0 < orientation (F a) (F b) (F c) ↔ 0 < orientation a b c) ∧
        (orientation (F a) (F b) (F c) < 0 ↔ orientation a b c < 0)
    rw [heq]
    constructor <;> constructor <;> intro h <;> nlinarith
  have hFGeneral : ∀ ⦃u v z : Fin s.card⦄,
      u ≠ v → u ≠ z → v ≠ z →
        orientation (F (e u).1) (F (e v).1) (F (e z).1) ≠ 0 := by
    intro u v z huv huz hvz
    have huve : (e u).1 ≠ (e v).1 := by
      intro h
      exact huv (e.injective (Subtype.ext h))
    have huze : (e u).1 ≠ (e z).1 := by
      intro h
      exact huz (e.injective (Subtype.ext h))
    have hvze : (e v).1 ≠ (e z).1 := by
      intro h
      exact hvz (e.injective (Subtype.ext h))
    have horig := hsGp (e u).property (e v).property (e z).property
      huve huze hvze
    have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hanchor := hraw.chart_anchor_pos hL
    have huDen := hraw.pool_denominator_pos i.isLt
      (hsSubset (e u).property)
    have hvDen := hraw.pool_denominator_pos i.isLt
      (hsSubset (e v).property)
    have hzDen := hraw.pool_denominator_pos i.isLt
      (hsSubset (e z).property)
    rw [sukAntichainChart_orientation
      (anchors 0) (anchors 1) (anchors (L + 2))
      (e u).1 (e v).1 (e z).1
      (ne_of_gt huDen) (ne_of_gt hvDen) (ne_of_gt hzDen)]
    apply mul_ne_zero
    · exact ne_of_gt <| div_pos (sq_pos_of_pos hanchor)
        (mul_pos (mul_pos huDen hvDen) hzDen)
    · exact horig
  let C : SweptConfiguration s.card :=
    { point := fun u ↦ F (e u).1
      sweep_strictMono := hFStrict
      generalPosition := hFGeneral }
  have hpoint : ∀ u, C.point u = F (e u).1 := fun _ ↦ rfl
  have hchoose :
      Nat.choose (capSize + n - 4) (capSize - 2) =
        Nat.choose (n + capSize - 4) (n - 2) := by
    rw [show capSize + n - 4 = n + capSize - 4 by omega]
    exact Nat.choose_symm_of_eq_add (by omega)
  have hlarge : Nat.choose (capSize + n - 4) (capSize - 2) < s.card := by
    rw [hchoose]
    exact hthreshold.trans_le hsLarge
  rcases CupCap.SweptConfiguration.hasCap_or_hasCup
      C hcapSize hn hlarge with hcap | hcup
  · rcases hcap with ⟨f, hf⟩
    let cap := sukAntichainSelected e f
    have hcapSubsetS : cap ⊆ s := sukAntichainSelected_subset e f
    have hcapSubset : cap ⊆ pools i.val := hcapSubsetS.trans hsSubset
    have hcapCard : cap.card = capSize := sukAntichainSelected_card e f
    have hchainNeg : ∀ ⦃u v z : Fin capSize⦄, u < v → v < z →
        orientation (e (f u)).1 (e (f v)).1 (e (f z)).1 < 0 := by
      intro u v z huv hvz
      have hcolor := hf.2 huv hvz
      have hchartNeg :=
        (C.turn_eq_right_iff (f u) (f v) (f z)
          (f.strictMono huv) (f.strictMono hvz)).mp hcolor
      apply (hFSigns (e (f u)).property
        (e (f v)).property (e (f z)).property).2.mp
      simpa [C] using hchartNeg
    have hsupported : SukRegionBaseSupportedCap
        (anchors i.val) (anchors (i.val + 3)) cap := by
      refine ⟨by rw [hcapCard]; exact hcapSize, ?_⟩
      intro p hp
      simp only [cap, sukAntichainSelected, Finset.mem_image,
        Finset.mem_univ, true_and] at hp
      obtain ⟨u, rfl⟩ := hp
      by_cases hu : u.val + 1 < capSize
      · let v : Fin capSize := ⟨u.val + 1, hu⟩
        have huv : u < v := by
          change u.val < u.val + 1
          omega
        refine ⟨(e (f v)).1, ?_, ?_, ?_, ?_⟩
        · simp [cap, sukAntichainSelected]
        · intro h
          have := e.injective (Subtype.ext h)
          exact (ne_of_lt (f.strictMono huv)) this
        · exact hsAnti.base_sameStrictSide hsSide hsBaseGp
            (hcapSubsetS (by simp [cap, sukAntichainSelected]))
            (hcapSubsetS (by simp [cap, sukAntichainSelected]))
            (by
              intro h
              have := e.injective (Subtype.ext h)
              exact (ne_of_lt (f.strictMono huv)) this)
        · intro z hz hzu hzv
          simp only [cap, sukAntichainSelected, Finset.mem_image,
            Finset.mem_univ, true_and] at hz
          obtain ⟨r, rfl⟩ := hz
          have hru : r ≠ u := by
            intro h
            subst r
            exact hzu rfl
          have hrv : r ≠ v := by
            intro h
            subst r
            exact hzv rfl
          have hbaseSide := hsAnti.base_sameStrictSide hsSide hsBaseGp
            (e (f u)).property (e (f v)).property
            (by
              intro h
              have := e.injective (Subtype.ext h)
              exact (ne_of_lt (f.strictMono huv)) this)
          have hsub := eOrder.strictMono (f.strictMono huv)
          change xi (eOrder (f u)).val.1 < xi (eOrder (f v)).val.1 at hsub
          have hxi : xi (e (f u)).1 < xi (e (f v)).1 := by
            simpa [e] using hsub
          have hbaseNeg := hraw.ordered_pair_baseLeft_neg i
            (hsSubset (e (f u)).property) (hsSubset (e (f v)).property)
            hxi hbaseSide
          have hzNeg : orientation (e (f u)).1 (e (f v)).1 (e (f r)).1 < 0 := by
            rcases lt_or_gt_of_ne hru with hru | hur
            · rw [orientation_cyclic]
              exact hchainNeg hru huv
            · have hvrLe : v ≤ r := by
                change u.val + 1 ≤ r.val
                omega
              have hvr : v < r := lt_of_le_of_ne hvrLe hrv.symm
              exact hchainNeg huv hvr
          exact Or.inl ⟨hbaseNeg, hzNeg⟩
      · have huLast : u.val + 1 = capSize := by omega
        have huPos : 0 < u.val := by omega
        let v : Fin capSize := ⟨u.val - 1, by omega⟩
        have hvu : v < u := by
          change u.val - 1 < u.val
          omega
        refine ⟨(e (f v)).1, ?_, ?_, ?_, ?_⟩
        · simp [cap, sukAntichainSelected]
        · intro h
          have := e.injective (Subtype.ext h)
          exact (ne_of_gt (f.strictMono hvu)) this
        · exact sameStrictSide_reverse_line <|
            hsAnti.base_sameStrictSide hsSide hsBaseGp
              (e (f v)).property (e (f u)).property
              (by
                intro h
                have := e.injective (Subtype.ext h)
                exact (ne_of_lt (f.strictMono hvu)) this)
        · intro z hz hzu hzv
          simp only [cap, sukAntichainSelected, Finset.mem_image,
            Finset.mem_univ, true_and] at hz
          obtain ⟨r, rfl⟩ := hz
          have hru : r ≠ u := by
            intro h
            subst r
            exact hzu rfl
          have hrv : r ≠ v := by
            intro h
            subst r
            exact hzv rfl
          have hbaseSide := hsAnti.base_sameStrictSide hsSide hsBaseGp
            (e (f v)).property (e (f u)).property
            (by
              intro h
              have := e.injective (Subtype.ext h)
              exact (ne_of_lt (f.strictMono hvu)) this)
          have hsub := eOrder.strictMono (f.strictMono hvu)
          change xi (eOrder (f v)).val.1 < xi (eOrder (f u)).val.1 at hsub
          have hxi : xi (e (f v)).1 < xi (e (f u)).1 := by
            simpa [e] using hsub
          have hbaseNeg := hraw.ordered_pair_baseLeft_neg i
            (hsSubset (e (f v)).property) (hsSubset (e (f u)).property)
            hxi hbaseSide
          have hzPos : 0 < orientation (e (f u)).1 (e (f v)).1 (e (f r)).1 := by
            have hrvOrder : r < v := by
              rcases lt_or_gt_of_ne hrv with hrv | hvr
              · exact hrv
              · exfalso
                have hruEq : r.val = u.val := by
                  change u.val - 1 < r.val at hvr
                  have hrBound := r.isLt
                  omega
                exact hru (Fin.ext hruEq)
            have hneg := hchainNeg hrvOrder hvu
            rw [← orientation_cyclic
              (e (f u)).1 (e (f v)).1 (e (f r)).1,
              orientation_swap (e (f r)).1 (e (f v)).1 (e (f u)).1]
            linarith
          have hbasePos : 0 < orientation
              (e (f u)).1 (e (f v)).1 (anchors i.val) := by
            rw [orientation_swap (e (f v)).1 (e (f u)).1 (anchors i.val)]
            linarith
          exact Or.inr ⟨hbasePos, hzPos⟩
    exact Or.inr ⟨cap, hcapSubset, hcapCard, hsupported⟩
  · rcases hcup with ⟨f, hf⟩
    let selected := sukAntichainSelected e f
    exact Or.inl ⟨selected,
      (sukAntichainSelected_subset e f).trans hsSubset,
      sukAntichainSelected_card e f,
      sukAntichainSelected_inConvexPosition hsGp F hFInj hFSigns e C
        hpoint f hf⟩

theorem SukConsecutiveRawPools.baseSupportedCaps_union
    {L capSize : ℕ}
    {anchors : ℕ → Point 2}
    {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    {selected : Finset (Fin L)}
    (hselected : PairwiseNonadjacent selected)
    (caps : Fin L → Finset (Point 2))
    (hcaps : ∀ i, i ∈ selected →
      caps i ⊆ pools i.val ∧
        (caps i).card = capSize ∧
          SukRegionBaseSupportedCap
            (anchors i.val) (anchors (i.val + 3)) (caps i)) :
    (selected : Set (Fin L)).PairwiseDisjoint caps ∧
      (selected.biUnion caps).card = selected.card * capSize ∧
        InConvexPosition (selected.biUnion caps) := by
  classical
  have hdisjoint : (selected : Set (Fin L)).PairwiseDisjoint caps := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    obtain ⟨q, hqi, hpq, hbase, -⟩ := (hcaps i hi).2.2.2 hpi
    have hremote := hraw.remote_sameStrictSide i j
      (hselected hi hj hij) ((hcaps i hi).1 hpi) ((hcaps i hi).1 hqi)
      ((hcaps j hj).1 hpj) hpq hbase
    rcases hremote with ⟨-, hpZero⟩ | ⟨-, hpZero⟩ <;> simp at hpZero
  have hcard : (selected.biUnion caps).card = selected.card * capSize := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      ∑ i ∈ selected, (caps i).card = ∑ _i ∈ selected, capSize := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hcaps i hi).2.1
      _ = selected.card * capSize := by simp
  have hsupport : ∀ ⦃p : Point 2⦄, p ∈ selected.biUnion caps →
      ∃ q ∈ selected.biUnion caps, ∃ common : Point 2,
        p ≠ q ∧ orientation p q common ≠ 0 ∧
          ∀ ⦃z : Point 2⦄, z ∈ selected.biUnion caps →
            z ≠ p → z ≠ q → SameStrictSide p q common z := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨q, hqi, hpq, hbase, hlocal⟩ := (hcaps i hi).2.2.2 hpi
    refine ⟨q, Finset.mem_biUnion.mpr ⟨i, hi, hqi⟩,
      anchors i.val, hpq, ?_, ?_⟩
    · rcases hbase with ⟨hleft, -⟩ | ⟨hleft, -⟩
      · exact ne_of_lt hleft
      · exact ne_of_gt hleft
    · intro z hz hzp hzq
      obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hz
      by_cases hij : i = j
      · subst j
        exact hlocal hzj hzp hzq
      · exact hraw.remote_sameStrictSide i j
          (hselected hi hj hij) ((hcaps i hi).1 hpi) ((hcaps i hi).1 hqi)
          ((hcaps j hj).1 hzj) hpq hbase
  exact ⟨hdisjoint, hcard,
    inConvexPosition_of_strict_vertex_support hsupport⟩

theorem SukConsecutiveRawPools.antichainPacking_containsConvexSubset
    {L n antiSize capSize : ℕ}
    {anchors : ℕ → Point 2}
    {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (hn : 2 ≤ n)
    (hcapSize : 2 ≤ capSize)
    (hthreshold :
      Nat.choose (n + capSize - 4) (n - 2) < antiSize)
    {selected : Finset (Fin L)}
    (hselected : PairwiseNonadjacent selected)
    (hanti : ∀ i, i ∈ selected →
      SukRegionHasAntichainSubset
        (anchors i.val) (anchors (i.val + 3))
        (pools i.val) antiSize)
    (hsize : n ≤ selected.card * capSize) :
    ContainsConvexSubset ((Finset.range L).biUnion pools) n := by
  classical
  have hlocal (i : Fin L) (hi : i ∈ selected) :=
    hraw.antichainSubset_cup_or_baseSupportedCap
      i (hanti i hi) hn hcapSize hthreshold
  by_cases himmediate : ∃ i, ∃ hi : i ∈ selected,
      ContainsConvexSubset (pools i.val) n
  · obtain ⟨i, -, t, htPool, htCard, htConvex⟩ := himmediate
    refine ⟨t, ?_, htCard, htConvex⟩
    intro p hp
    exact Finset.mem_biUnion.mpr
      ⟨i.val, Finset.mem_range.mpr i.isLt, htPool hp⟩
  · have hcapExists : ∀ i, i ∈ selected →
        ∃ cap : Finset (Point 2),
          cap ⊆ pools i.val ∧ cap.card = capSize ∧
            SukRegionBaseSupportedCap
              (anchors i.val) (anchors (i.val + 3)) cap := by
      intro i hi
      rcases hlocal i hi with hcup | hcap
      · exact (himmediate ⟨i, hi, hcup⟩).elim
      · exact hcap
    let caps : Fin L → Finset (Point 2) := fun i ↦
      if hi : i ∈ selected then (hcapExists i hi).choose else ∅
    have hcaps : ∀ i, i ∈ selected →
        caps i ⊆ pools i.val ∧ (caps i).card = capSize ∧
          SukRegionBaseSupportedCap
            (anchors i.val) (anchors (i.val + 3)) (caps i) := by
      intro i hi
      simpa [caps, hi] using (hcapExists i hi).choose_spec
    have hunion := hraw.baseSupportedCaps_union hselected caps hcaps
    obtain ⟨exactSet, hexactSubset, hexactCard⟩ :=
      Finset.exists_subset_card_eq (hunion.2.1.symm ▸ hsize)
    refine ⟨exactSet, ?_, hexactCard, hunion.2.2.mono hexactSubset⟩
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp (hexactSubset hp)
    exact Finset.mem_biUnion.mpr
      ⟨i.val, Finset.mem_range.mpr i.isLt, (hcaps i hi).1 hpi⟩

end

end ErdosSzekeres

end
