module

public import ErdosSzekeres.HMPTHorizontalChainDefs
public import ErdosSzekeres.HMPTSpikeOrderGeometry

@[expose] public section

/-!
# Horizontal triple-color geometry in one HMPT spike pool

This module derives the literal five-point color semantics and four-point
transitivity required by the third HMPT finite layer.  Its only geometric
input is `SukRegionGeometry`; in particular, no horizontal-chain selection or
downstream cyclic conclusion is used.
-/

namespace ErdosSzekeres

noncomputable section

open Set
open scoped Convex

/-- The Cramer bridge from the literal crossed-segment relation to its two
strict outer-anchor orientation signs. -/
private theorem crossed_segments_nonempty_iff_orientation_neg_h3
    (outerLeft outerRight p q : Point 2)
    (hp : 0 < orientation outerLeft outerRight p)
    (hq : 0 < orientation outerLeft outerRight q)
    (hleft : orientation outerLeft p q ≠ 0)
    (hright : orientation outerRight p q ≠ 0) :
    Set.Nonempty
        (convexHull ℝ ({outerLeft, q} : Set (Point 2)) ∩
          convexHull ℝ ({outerRight, p} : Set (Point 2))) ↔
      orientation outerLeft p q < 0 ∧ orientation outerRight p q < 0 := by
  constructor
  · rintro ⟨x, hxLeft, hxRight⟩
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
  · rintro ⟨hleftNeg, hrightNeg⟩
    let hp' := orientation outerLeft outerRight p
    let hq' := orientation outerLeft outerRight q
    let left := orientation outerLeft p q
    let right := orientation outerRight p q
    let denominator := hp' - right
    let t := hp' / denominator
    let u := hq' / denominator
    have hdenPos : 0 < denominator := by
      dsimp [hp', right]
      linarith
    have hdenEq : hq' - left = denominator := by
      dsimp [denominator, hp', hq', left, right]
      simp only [orientation]
      ring
    have htPos : 0 < t := div_pos hp hdenPos
    have huPos : 0 < u := div_pos hq hdenPos
    have htLt : t < 1 := by
      apply (div_lt_one hdenPos).2
      dsimp [hp', right]
      linarith
    have huLt : u < 1 := by
      apply (div_lt_one hdenPos).2
      rw [← hdenEq]
      linarith
    let x : Point 2 := (1 - t) • outerLeft + t • q
    refine ⟨x, ?_, ?_⟩
    · rw [convexHull_pair, segment_eq_image]
      exact ⟨t, ⟨htPos.le, htLt.le⟩, rfl⟩
    · rw [convexHull_pair, segment_eq_image]
      refine ⟨u, ⟨huPos.le, huLt.le⟩, ?_⟩
      dsimp [x, t, u]
      funext i
      fin_cases i <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      all_goals
        field_simp [ne_of_gt hdenPos]
        dsimp [denominator, hp', hq', left, right]
        simp only [orientation, Fin.isValue]
        ring

/-- Negative orientation relative to either outer anchor is transitive among
points strictly above the common base. -/
private theorem fixed_anchor_orientation_trans_h3
    (outerLeft outerRight anchor p q r : Point 2)
    (hanchor : anchor = outerLeft ∨ anchor = outerRight)
    (hp : 0 < orientation outerLeft outerRight p)
    (hq : 0 < orientation outerLeft outerRight q)
    (hr : 0 < orientation outerLeft outerRight r)
    (hpq : orientation anchor p q < 0)
    (hqr : orientation anchor q r < 0) :
    orientation anchor p r < 0 := by
  have hidentity :
      orientation anchor p q * orientation outerLeft outerRight r +
          orientation anchor q r * orientation outerLeft outerRight p =
        orientation anchor p r * orientation outerLeft outerRight q := by
    rcases hanchor with hanchor | hanchor
    · subst anchor
      simp only [orientation]
      ring
    · subst anchor
      simp only [orientation]
      ring
  have hfirst :
      orientation anchor p q * orientation outerLeft outerRight r < 0 :=
    mul_neg_of_neg_of_pos hpq hr
  have hsecond :
      orientation anchor q r * orientation outerLeft outerRight p < 0 :=
    mul_neg_of_neg_of_pos hqr hp
  nlinarith

/-- A four-point set behind one anchor is convex exactly in the negative
orientation branch of its three moving points. -/
private theorem anchored_convex_iff_orientation_neg_h3
    (a p q r : Point 2)
    (hapq : orientation a p q < 0)
    (hapr : orientation a p r < 0)
    (haqr : orientation a q r < 0)
    (hpqr : orientation p q r ≠ 0) :
    InConvexPosition {a, p, q, r} ↔ orientation p q r < 0 := by
  have hap : a ≠ p := by
    intro h
    subst p
    simp at hapq
  have haq : a ≠ q := by
    intro h
    subst q
    simp at hapq
  have har : a ≠ r := by
    intro h
    subst r
    simp at hapr
  have hpq : p ≠ q := by
    intro h
    subst q
    simp at hapq
  have hpr : p ≠ r := by
    intro h
    subst r
    simp at hapr
  have hqr : q ≠ r := by
    intro h
    subst r
    simp at haqr
  constructor
  · intro hconvex
    rcases lt_or_gt_of_ne hpqr with hpqrNeg | hpqrPos
    · exact hpqrNeg
    · have hinside : q ∈ convexHull ℝ (triangle a p r) :=
        (mem_convexHull_triangle_iff_of_orientation_neg a p r q hapr).2
          ⟨hapq.le, by rw [orientation_swap_last]; linarith,
            by simpa [orientation_cyclic] using haqr.le⟩
      have houtside :=
        (inConvexPosition_four_iff_no_mem_triangle
          a p q r hap haq har hpq hpr hqr).1 hconvex
      exact (houtside.2.2.1 hinside).elim
  · exact inConvexPosition_four_of_all_orientation_neg a p q r
      hapq hapr haqr

/-- A five-point GP set is convex once each of its one-point erasures is
convex. -/
private theorem inConvexPosition_card_five_of_erase_h3
    (u : Finset (Point 2)) (hgp : InGeneralPosition u)
    (hcard : u.card = 5)
    (herase : ∀ x ∈ u, InConvexPosition (u.erase x)) :
    InConvexPosition u := by
  apply (inConvexPosition_iff_four_subsets u hgp).2
  intro t htu htcard
  obtain ⟨x, hxu, hxt⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show t.card < u.card by omega)
  have htErase : t ⊆ u.erase x := by
    intro y hyt
    apply Finset.mem_erase.mpr
    exact ⟨by
      intro hyx
      subst y
      exact hxt hyt, htu hyt⟩
  have htEq : t = u.erase x := by
    apply Finset.eq_of_subset_of_card_le htErase
    rw [Finset.card_erase_of_mem hxu, hcard, htcard]
  rw [htEq]
  exact herase x hxu

/-- The projective chart used to linearize the horizontal order. -/
private def hmptHorizontalProjectiveChart
    (outerLeft rightAnchor outerRight p : Point 2) : Point 2 :=
  ![orientation outerLeft p rightAnchor /
      orientation outerLeft outerRight p,
    -orientation outerLeft outerRight rightAnchor /
      orientation outerLeft outerRight p]

private theorem hmptHorizontalProjectiveChart_orientation
    (outerLeft rightAnchor outerRight p q r : Point 2)
    (hp : orientation outerLeft outerRight p ≠ 0)
    (hq : orientation outerLeft outerRight q ≠ 0)
    (hr : orientation outerLeft outerRight r ≠ 0) :
    orientation
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight p)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight q)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight r) =
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

private theorem hmptHorizontalProjectiveChart_first_difference
    (outerLeft rightAnchor outerRight p q : Point 2)
    (hp : orientation outerLeft outerRight p ≠ 0)
    (hq : orientation outerLeft outerRight q ≠ 0) :
    (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight q) 0 -
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight p) 0 =
      orientation outerLeft outerRight rightAnchor *
          orientation p outerLeft q /
        (orientation outerLeft outerRight p *
          orientation outerLeft outerRight q) := by
  simp only [hmptHorizontalProjectiveChart, Matrix.cons_val_zero]
  field_simp
  simp only [orientation]
  ring

private theorem orientation_transitive_of_firstCoord_lt_pos_h3
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

private theorem orientation_transitive_of_firstCoord_lt_neg_h3
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

private theorem hmptHorizontalProjectiveChart_orientation_pos_iff
    (outerLeft rightAnchor outerRight p q r : Point 2)
    (hanchor : 0 < orientation outerLeft outerRight rightAnchor)
    (hp : 0 < orientation outerLeft outerRight p)
    (hq : 0 < orientation outerLeft outerRight q)
    (hr : 0 < orientation outerLeft outerRight r) :
    0 < orientation
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight p)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight q)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight r) ↔
      0 < orientation p q r := by
  rw [hmptHorizontalProjectiveChart_orientation outerLeft rightAnchor outerRight
    p q r (ne_of_gt hp) (ne_of_gt hq) (ne_of_gt hr)]
  have hfactor : 0 < orientation outerLeft outerRight rightAnchor ^ 2 /
      (orientation outerLeft outerRight p *
        orientation outerLeft outerRight q *
        orientation outerLeft outerRight r) :=
    div_pos (sq_pos_of_pos hanchor) (mul_pos (mul_pos hp hq) hr)
  exact mul_pos_iff_of_pos_left hfactor

private theorem hmptHorizontalProjectiveChart_orientation_neg_iff
    (outerLeft rightAnchor outerRight p q r : Point 2)
    (hanchor : 0 < orientation outerLeft outerRight rightAnchor)
    (hp : 0 < orientation outerLeft outerRight p)
    (hq : 0 < orientation outerLeft outerRight q)
    (hr : 0 < orientation outerLeft outerRight r) :
    orientation
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight p)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight q)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight r) < 0 ↔
      orientation p q r < 0 := by
  rw [hmptHorizontalProjectiveChart_orientation outerLeft rightAnchor outerRight
    p q r (ne_of_gt hp) (ne_of_gt hq) (ne_of_gt hr)]
  have hfactor : 0 < orientation outerLeft outerRight rightAnchor ^ 2 /
      (orientation outerLeft outerRight p *
        orientation outerLeft outerRight q *
        orientation outerLeft outerRight r) :=
    div_pos (sq_pos_of_pos hanchor) (mul_pos (mul_pos hp hq) hr)
  constructor
  · intro hproduct
    exact neg_of_mul_neg_right hproduct hfactor.le
  · exact mul_neg_of_pos_of_neg hfactor

private theorem hmptHorizontalTripleColor_eq_right_iff
    {s : Finset (Point 2)} (p q r : ↥s) :
    hmptHorizontalTripleColor p q r = Turn.right ↔
      orientation p.1 q.1 r.1 < 0 := by
  simp [hmptHorizontalTripleColor]

private theorem hmptHorizontalTripleColor_eq_left_iff_of_ne
    {s : Finset (Point 2)} (p q r : ↥s)
    (hne : orientation p.1 q.1 r.1 ≠ 0) :
    hmptHorizontalTripleColor p q r = Turn.left ↔
      0 < orientation p.1 q.1 r.1 := by
  simp only [hmptHorizontalTripleColor]
  by_cases hneg : orientation p.1 q.1 r.1 < 0
  · constructor
    · intro hfalse
      simp [hneg] at hfalse
    · intro hpos
      exfalso
      linarith
  · have hpos : 0 < orientation p.1 q.1 r.1 :=
      lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hne)
    constructor
    · intro _
      exact hpos
    · intro _
      simp [hneg]

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem outerLeft_ne_point_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) : outerLeft ≠ p.1 := by
  intro heq
  have hp := h.base_orientation_pos p
  rw [heq] at hp
  simp at hp

private theorem outerRight_ne_point_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) : outerRight ≠ p.1 := by
  intro heq
  have hp := h.base_orientation_pos p
  rw [heq] at hp
  simp at hp

private theorem outerLeft_ne_outerRight_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s) :
    outerLeft ≠ outerRight := by
  intro heq
  have hanchor := h.anchorsCap.orient013
  rw [heq] at hanchor
  simp at hanchor

private theorem outer_pair_generalPosition_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) :
    InGeneralPosition {outerLeft, outerRight, p.1, q.1} := by
  apply h.generalPosition.mono
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp [p.property]
  · simp [q.property]

private theorem pair_orientations_ne_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : p.1 ≠ q.1) :
    orientation outerLeft p.1 q.1 ≠ 0 ∧
      orientation outerRight p.1 q.1 ≠ 0 := by
  have hgp := h.outer_pair_generalPosition_h3 p q
  exact ⟨hgp (by simp) (by simp) (by simp)
      (h.outerLeft_ne_point_h3 p) (h.outerLeft_ne_point_h3 q) hpq,
    hgp (by simp) (by simp) (by simp)
      (h.outerRight_ne_point_h3 p) (h.outerRight_ne_point_h3 q) hpq⟩

private theorem horizontalLT_iff_orientation_signs_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) :
    HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1 ↔
      orientation outerLeft p.1 q.1 < 0 ∧
        orientation outerRight p.1 q.1 < 0 := by
  constructor
  · rintro ⟨hpq, hintersection⟩
    have hne := h.pair_orientations_ne_h3 p q hpq
    exact (crossed_segments_nonempty_iff_orientation_neg_h3
      outerLeft outerRight p.1 q.1
      (h.base_orientation_pos p) (h.base_orientation_pos q)
      hne.1 hne.2).mp hintersection
  · intro hsigns
    have hpq : p.1 ≠ q.1 := by
      intro heq
      rw [heq] at hsigns
      simp at hsigns
    have hne := h.pair_orientations_ne_h3 p q hpq
    exact ⟨hpq, (crossed_segments_nonempty_iff_orientation_neg_h3
      outerLeft outerRight p.1 q.1
      (h.base_orientation_pos p) (h.base_orientation_pos q)
      hne.1 hne.2).mpr hsigns⟩

private theorem horizontalLT_trans_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1)
    (hqr : HMPTSpikeHorizontalLT outerLeft outerRight q.1 r.1) :
    HMPTSpikeHorizontalLT outerLeft outerRight p.1 r.1 := by
  apply (h.horizontalLT_iff_orientation_signs_h3 p r).2
  have hpqSigns := (h.horizontalLT_iff_orientation_signs_h3 p q).1 hpq
  have hqrSigns := (h.horizontalLT_iff_orientation_signs_h3 q r).1 hqr
  exact ⟨fixed_anchor_orientation_trans_h3 outerLeft outerRight outerLeft
      p.1 q.1 r.1 (Or.inl rfl) (h.base_orientation_pos p)
      (h.base_orientation_pos q) (h.base_orientation_pos r)
      hpqSigns.1 hqrSigns.1,
    fixed_anchor_orientation_trans_h3 outerLeft outerRight outerRight
      p.1 q.1 r.1 (Or.inr rfl) (h.base_orientation_pos p)
      (h.base_orientation_pos q) (h.base_orientation_pos r)
      hpqSigns.2 hqrSigns.2⟩

private theorem horizontal_triple_orientation_ne_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1)
    (hqr : HMPTSpikeHorizontalLT outerLeft outerRight q.1 r.1) :
    orientation p.1 q.1 r.1 ≠ 0 := by
  have hpr := h.horizontalLT_trans_h3 p q r hpq hqr
  exact h.generalPosition (by simp [p.property])
    (by simp [q.property]) (by simp [r.property])
    hpq.1 hpr.1 hqr.1

private theorem outer_pair_convex_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1) :
    InConvexPosition {outerLeft, outerRight, p.1, q.1} := by
  have hsigns := (h.horizontalLT_iff_orientation_signs_h3 p q).1 hpq
  have hpBase := h.base_orientation_pos p
  have hqBase := h.base_orientation_pos q
  have hApD : orientation outerLeft p.1 outerRight < 0 := by
    rw [orientation_swap_last]
    linarith
  have hAqD : orientation outerLeft q.1 outerRight < 0 := by
    rw [orientation_swap_last]
    linarith
  have hpqD : orientation p.1 q.1 outerRight < 0 := by
    rw [orientation_cyclic outerRight p.1 q.1]
    exact hsigns.2
  have hconvex := inConvexPosition_four_of_all_orientation_neg
    outerLeft p.1 q.1 outerRight hsigns.1 hApD hAqD hpqD
  rw [show ({outerLeft, p.1, q.1, outerRight} : Finset (Point 2)) =
      {outerLeft, outerRight, p.1, q.1} by
    ext x
    simp [or_comm, or_left_comm]] at hconvex
  exact hconvex

private theorem horizontal_five_convex_iff_orientation_neg_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1)
    (hqr : HMPTSpikeHorizontalLT outerLeft outerRight q.1 r.1) :
    InConvexPosition {outerLeft, outerRight, p.1, q.1, r.1} ↔
      orientation p.1 q.1 r.1 < 0 := by
  have hpr := h.horizontalLT_trans_h3 p q r hpq hqr
  have hpqSigns := (h.horizontalLT_iff_orientation_signs_h3 p q).1 hpq
  have hprSigns := (h.horizontalLT_iff_orientation_signs_h3 p r).1 hpr
  have hqrSigns := (h.horizontalLT_iff_orientation_signs_h3 q r).1 hqr
  have htripleNe := h.horizontal_triple_orientation_ne_h3 p q r hpq hqr
  have hleftClass := anchored_convex_iff_orientation_neg_h3
    outerLeft p.1 q.1 r.1 hpqSigns.1 hprSigns.1 hqrSigns.1 htripleNe
  have hrightClass := anchored_convex_iff_orientation_neg_h3
    outerRight p.1 q.1 r.1 hpqSigns.2 hprSigns.2 hqrSigns.2 htripleNe
  constructor
  · intro hconvex
    apply hleftClass.1
    exact hconvex.mono (by simp)
  · intro hnegative
    have hleftConvex := hleftClass.2 hnegative
    have hrightConvex := hrightClass.2 hnegative
    have hpqConvex := h.outer_pair_convex_h3 p q hpq
    have hprConvex := h.outer_pair_convex_h3 p r hpr
    have hqrConvex := h.outer_pair_convex_h3 q r hqr
    let u : Finset (Point 2) :=
      {outerLeft, outerRight, p.1, q.1, r.1}
    have hgp : InGeneralPosition u := by
      apply h.generalPosition.mono
      intro x hx
      simp only [u, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · simp
      · simp
      · simp [p.property]
      · simp [q.property]
      · simp [r.property]
    have hAD := h.outerLeft_ne_outerRight_h3
    have hAp := h.outerLeft_ne_point_h3 p
    have hAq := h.outerLeft_ne_point_h3 q
    have hAr := h.outerLeft_ne_point_h3 r
    have hDp := h.outerRight_ne_point_h3 p
    have hDq := h.outerRight_ne_point_h3 q
    have hDr := h.outerRight_ne_point_h3 r
    have hcard : u.card = 5 := by
      dsimp [u]
      simp [hAD, hAp, hAq, hAr, hDp, hDq, hDr,
        hpq.1, hpr.1, hqr.1]
    have hArest : outerLeft ∉ ({outerRight, p.1, q.1, r.1} :
        Finset (Point 2)) := by
      simp [hAD, hAp, hAq, hAr]
    have hDrest : outerRight ∉ ({p.1, q.1, r.1} :
        Finset (Point 2)) := by
      simp [hDp, hDq, hDr]
    have hPrest : p.1 ∉ ({q.1, r.1} : Finset (Point 2)) := by
      simp [hpq.1, hpr.1]
    have hQrest : q.1 ∉ ({r.1} : Finset (Point 2)) := by
      simp [hqr.1]
    have heraseA : u.erase outerLeft = {outerRight, p.1, q.1, r.1} := by
      dsimp [u]
      exact Finset.erase_insert hArest
    have heraseD : u.erase outerRight = {outerLeft, p.1, q.1, r.1} := by
      dsimp [u]
      rw [Finset.erase_insert_of_ne hAD, Finset.erase_insert hDrest]
    have heraseP : u.erase p.1 = {outerLeft, outerRight, q.1, r.1} := by
      dsimp [u]
      rw [Finset.erase_insert_of_ne hAp, Finset.erase_insert_of_ne hDp,
        Finset.erase_insert hPrest]
    have heraseQ : u.erase q.1 = {outerLeft, outerRight, p.1, r.1} := by
      dsimp [u]
      rw [Finset.erase_insert_of_ne hAq, Finset.erase_insert_of_ne hDq,
        Finset.erase_insert_of_ne hpq.1, Finset.erase_insert hQrest]
    have heraseR : u.erase r.1 = {outerLeft, outerRight, p.1, q.1} := by
      dsimp [u]
      rw [Finset.erase_insert_of_ne hAr, Finset.erase_insert_of_ne hDr,
        Finset.erase_insert_of_ne hpr.1, Finset.erase_insert_of_ne hqr.1,
        Finset.erase_singleton, Finset.insert_empty]
    apply inConvexPosition_card_five_of_erase_h3 u hgp hcard
    intro x hx
    simp only [u, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx | hx
    · subst x
      rw [heraseA]
      exact hrightConvex
    · subst x
      rw [heraseD]
      exact hleftConvex
    · subst x
      rw [heraseP]
      exact hqrConvex
    · subst x
      rw [heraseQ]
      exact hprConvex
    · subst x
      rw [heraseR]
      exact hpqConvex

private theorem horizontal_chart_first_lt_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1) :
    (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight p.1) 0 <
      (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight q.1) 0 := by
  have hp := h.base_orientation_pos p
  have hq := h.base_orientation_pos q
  have hsigns := (h.horizontalLT_iff_orientation_signs_h3 p q).1 hpq
  have hpAq : 0 < orientation p.1 outerLeft q.1 := by
    rw [← orientation_cyclic p.1 outerLeft q.1,
      orientation_swap_last outerLeft p.1 q.1]
    linarith
  have hanchor : 0 < orientation outerLeft outerRight rightAnchor := by
    rw [orientation_swap_last]
    linarith [h.anchorsCap.orient013]
  have hdiff : 0 <
      (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight q.1) 0 -
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight p.1) 0 := by
    rw [hmptHorizontalProjectiveChart_first_difference
      outerLeft rightAnchor outerRight p.1 q.1 (ne_of_gt hp) (ne_of_gt hq)]
    exact div_pos (mul_pos hanchor hpAq) (mul_pos hp hq)
  linarith

private theorem horizontal_transitiveColoring_h3
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s) :
    HMPTHorizontalTransitiveColoring outerLeft outerRight
      (hmptHorizontalTripleColor (s := s)) := by
  intro p q r t hpq hqr hrt c hpqr hqrt
  have hp := h.base_orientation_pos p
  have hq := h.base_orientation_pos q
  have hr := h.base_orientation_pos r
  have ht := h.base_orientation_pos t
  have hanchor : 0 < orientation outerLeft outerRight rightAnchor := by
    rw [orientation_swap_last]
    linarith [h.anchorsCap.orient013]
  have hpqX := h.horizontal_chart_first_lt_h3 p q hpq
  have hqrX := h.horizontal_chart_first_lt_h3 q r hqr
  have hrtX := h.horizontal_chart_first_lt_h3 r t hrt
  have hpr := h.horizontalLT_trans_h3 p q r hpq hqr
  have hqt := h.horizontalLT_trans_h3 q r t hqr hrt
  have hpqrNe := h.horizontal_triple_orientation_ne_h3 p q r hpq hqr
  have hqrtNe := h.horizontal_triple_orientation_ne_h3 q r t hqr hrt
  have hpqtNe := h.horizontal_triple_orientation_ne_h3 p q t hpq hqt
  have hprtNe := h.horizontal_triple_orientation_ne_h3 p r t hpr hrt
  cases c with
  | left =>
      have hpqrPos :=
        (hmptHorizontalTripleColor_eq_left_iff_of_ne p q r hpqrNe).1 hpqr
      have hqrtPos :=
        (hmptHorizontalTripleColor_eq_left_iff_of_ne q r t hqrtNe).1 hqrt
      have hchartPqr :=
        (hmptHorizontalProjectiveChart_orientation_pos_iff
          outerLeft rightAnchor outerRight p.1 q.1 r.1
          hanchor hp hq hr).2 hpqrPos
      have hchartQrt :=
        (hmptHorizontalProjectiveChart_orientation_pos_iff
          outerLeft rightAnchor outerRight q.1 r.1 t.1
          hanchor hq hr ht).2 hqrtPos
      have hout := orientation_transitive_of_firstCoord_lt_pos_h3
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight p.1)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight q.1)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight r.1)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight t.1)
        hpqX hqrX hrtX hchartPqr hchartQrt
      have hpqtPos :=
        (hmptHorizontalProjectiveChart_orientation_pos_iff
          outerLeft rightAnchor outerRight p.1 q.1 t.1
          hanchor hp hq ht).1 hout.1
      have hprtPos :=
        (hmptHorizontalProjectiveChart_orientation_pos_iff
          outerLeft rightAnchor outerRight p.1 r.1 t.1
          hanchor hp hr ht).1 hout.2
      exact ⟨(hmptHorizontalTripleColor_eq_left_iff_of_ne
          p q t hpqtNe).2 hpqtPos,
        (hmptHorizontalTripleColor_eq_left_iff_of_ne
          p r t hprtNe).2 hprtPos⟩
  | right =>
      have hpqrNeg :=
        (hmptHorizontalTripleColor_eq_right_iff p q r).1 hpqr
      have hqrtNeg :=
        (hmptHorizontalTripleColor_eq_right_iff q r t).1 hqrt
      have hchartPqr :=
        (hmptHorizontalProjectiveChart_orientation_neg_iff
          outerLeft rightAnchor outerRight p.1 q.1 r.1
          hanchor hp hq hr).2 hpqrNeg
      have hchartQrt :=
        (hmptHorizontalProjectiveChart_orientation_neg_iff
          outerLeft rightAnchor outerRight q.1 r.1 t.1
          hanchor hq hr ht).2 hqrtNeg
      have hout := orientation_transitive_of_firstCoord_lt_neg_h3
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight p.1)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight q.1)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight r.1)
        (hmptHorizontalProjectiveChart outerLeft rightAnchor outerRight t.1)
        hpqX hqrX hrtX hchartPqr hchartQrt
      have hpqtNeg :=
        (hmptHorizontalProjectiveChart_orientation_neg_iff
          outerLeft rightAnchor outerRight p.1 q.1 t.1
          hanchor hp hq ht).1 hout.1
      have hprtNeg :=
        (hmptHorizontalProjectiveChart_orientation_neg_iff
          outerLeft rightAnchor outerRight p.1 r.1 t.1
          hanchor hp hr ht).1 hout.2
      exact ⟨(hmptHorizontalTripleColor_eq_right_iff p q t).2 hpqtNeg,
        (hmptHorizontalTripleColor_eq_right_iff p r t).2 hprtNeg⟩

/-- Raw Suk-region geometry supplies the exact local geometry used by the HMPT
horizontal recurrence: negative/right triples are precisely the five-point
convex ones, and both colors are transitive along the literal strict
horizontal order. -/
theorem hmptHorizontalTripleGeometry
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s) :
    HMPTHorizontalTripleGeometry outerLeft outerRight
      (hmptHorizontalTripleColor (s := s)) := by
  refine ⟨h.horizontal_transitiveColoring_h3, ?_⟩
  intro p q r hpq hqr
  have hclass :=
    h.horizontal_five_convex_iff_orientation_neg_h3 p q r hpq hqr
  constructor
  · rw [hclass]
    exact hmptHorizontalTripleColor_eq_right_iff p q r
  · rw [hclass]
    simp [hmptHorizontalTripleColor]

end SukRegionGeometry

end

end ErdosSzekeres

end
