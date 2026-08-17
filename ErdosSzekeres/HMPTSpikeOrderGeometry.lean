module

public import ErdosSzekeres.HMPTSpikeOrderDefs
public import ErdosSzekeres.SukRegionChainGeometry

@[expose] public section

/-!
# Geometric production of the HMPT spike orders

This module derives the two HMPT spike orders and their exclusive comparability
directly from `SukRegionGeometry`.  The horizontal relation keeps its literal
closed-segment intersection semantics; private orientation lemmas expose the
projective sign coordinates used to prove its order laws.
-/

namespace ErdosSzekeres

noncomputable section

open Set
open scoped Convex

private theorem convexHull_triangle_subset_iff_sukRegionLE
    (outerLeft outerRight p q : Point 2) :
    convexHull ℝ (triangle outerLeft outerRight p) ⊆
        convexHull ℝ (triangle outerLeft outerRight q) ↔
      SukRegionLE outerLeft outerRight q p := by
  constructor
  · intro hsub
    exact hsub (subset_convexHull ℝ _ (by simp [triangle]))
  · intro hp
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    simp only [triangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (by simp [triangle])
    · exact subset_convexHull ℝ _ (by simp [triangle])
    · exact hp

private theorem hmptSpikeVerticalLE_iff_sukRegionLE_reverse
    (outerLeft outerRight p q : Point 2) :
    HMPTSpikeVerticalLE outerLeft outerRight p q ↔
      SukRegionLE outerLeft outerRight q p := by
  constructor
  · rintro (rfl | hpq)
    · exact sukRegionLE_refl outerLeft outerRight p
    · exact (convexHull_triangle_subset_iff_sukRegionLE
        outerLeft outerRight p q).mp hpq.2
  · intro hpq
    by_cases heq : p = q
    · exact Or.inl heq
    · exact Or.inr ⟨heq,
        (convexHull_triangle_subset_iff_sukRegionLE
          outerLeft outerRight p q).mpr hpq⟩

/-- The exact Cramer bridge for the source's crossed closed segments. -/
private theorem crossed_segments_nonempty_iff_orientation_neg
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

private theorem fixed_anchor_orientation_trans
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

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem outerLeft_ne_point
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) : outerLeft ≠ p.1 := by
  intro heq
  have hp := h.base_orientation_pos p
  rw [heq] at hp
  simp at hp

private theorem outerRight_ne_point
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) : outerRight ≠ p.1 := by
  intro heq
  have hp := h.base_orientation_pos p
  rw [heq] at hp
  simp at hp

private theorem outer_pair_generalPosition
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

private theorem pair_orientations_ne
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : p.1 ≠ q.1) :
    orientation outerLeft p.1 q.1 ≠ 0 ∧
      orientation outerRight p.1 q.1 ≠ 0 := by
  have hgp := h.outer_pair_generalPosition p q
  exact ⟨hgp (by simp) (by simp) (by simp)
      (h.outerLeft_ne_point p) (h.outerLeft_ne_point q) hpq,
    hgp (by simp) (by simp) (by simp)
      (h.outerRight_ne_point p) (h.outerRight_ne_point q) hpq⟩

private theorem verticalLT_iff_orientation_signs
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) :
    HMPTSpikeVerticalLT outerLeft outerRight p.1 q.1 ↔
      0 < orientation outerLeft p.1 q.1 ∧
        orientation outerRight p.1 q.1 < 0 := by
  constructor
  · rintro ⟨hpq, hsub⟩
    have hinside := (mem_convexHull_triangle_iff_of_orientation_pos
      outerLeft outerRight q.1 p.1 (h.base_orientation_pos q)).mp
        ((convexHull_triangle_subset_iff_sukRegionLE
          outerLeft outerRight p.1 q.1).mp hsub)
    have hne := h.pair_orientations_ne p q hpq
    have hleftWeak : 0 ≤ orientation outerLeft p.1 q.1 := by
      rw [orientation_cyclic q.1 outerLeft p.1]
      exact hinside.2.2
    have hrightWeak : orientation outerRight p.1 q.1 ≤ 0 := by
      rw [orientation_swap_last outerRight p.1 q.1] at hinside
      linarith [hinside.2.1]
    exact ⟨lt_of_le_of_ne hleftWeak (Ne.symm hne.1),
      lt_of_le_of_ne hrightWeak hne.2⟩
  · rintro ⟨hleftPos, hrightNeg⟩
    have hpq : p.1 ≠ q.1 := by
      intro heq
      rw [heq] at hleftPos
      simp at hleftPos
    refine ⟨hpq, (convexHull_triangle_subset_iff_sukRegionLE
      outerLeft outerRight p.1 q.1).mpr ?_⟩
    apply (mem_convexHull_triangle_iff_of_orientation_pos
      outerLeft outerRight q.1 p.1 (h.base_orientation_pos q)).mpr
    refine ⟨(h.base_orientation_pos p).le, ?_, ?_⟩
    · rw [orientation_swap_last outerRight p.1 q.1]
      linarith
    · rw [← orientation_cyclic q.1 outerLeft p.1]
      exact hleftPos.le

private theorem horizontalLT_iff_orientation_signs
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) :
    HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1 ↔
      orientation outerLeft p.1 q.1 < 0 ∧
        orientation outerRight p.1 q.1 < 0 := by
  constructor
  · rintro ⟨hpq, hintersection⟩
    have hne := h.pair_orientations_ne p q hpq
    exact (crossed_segments_nonempty_iff_orientation_neg
      outerLeft outerRight p.1 q.1
      (h.base_orientation_pos p) (h.base_orientation_pos q)
      hne.1 hne.2).mp hintersection
  · intro hsigns
    have hpq : p.1 ≠ q.1 := by
      intro heq
      rw [heq] at hsigns
      simp at hsigns
    have hne := h.pair_orientations_ne p q hpq
    exact ⟨hpq, (crossed_segments_nonempty_iff_orientation_neg
      outerLeft outerRight p.1 q.1
      (h.base_orientation_pos p) (h.base_orientation_pos q)
      hne.1 hne.2).mpr hsigns⟩

private theorem verticalLE_iff_orientation_signs_of_ne
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : p.1 ≠ q.1) :
    HMPTSpikeVerticalLE outerLeft outerRight p.1 q.1 ↔
      0 < orientation outerLeft p.1 q.1 ∧
        orientation outerRight p.1 q.1 < 0 := by
  rw [HMPTSpikeVerticalLE, h.verticalLT_iff_orientation_signs p q]
  simp [hpq]

private theorem horizontalLE_iff_orientation_signs_of_ne
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : p.1 ≠ q.1) :
    HMPTSpikeHorizontalLE outerLeft outerRight p.1 q.1 ↔
      orientation outerLeft p.1 q.1 < 0 ∧
        orientation outerRight p.1 q.1 < 0 := by
  rw [HMPTSpikeHorizontalLE, h.horizontalLT_iff_orientation_signs p q]
  simp [hpq]

private theorem horizontalLE_trans
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : HMPTSpikeHorizontalLE outerLeft outerRight p.1 q.1)
    (hqr : HMPTSpikeHorizontalLE outerLeft outerRight q.1 r.1) :
    HMPTSpikeHorizontalLE outerLeft outerRight p.1 r.1 := by
  rcases hpq with hpq | hpq
  · rcases hqr with hqr | hqr
    · exact Or.inl (hpq.trans hqr)
    · exact Or.inr (by simpa only [hpq] using hqr)
  · rcases hqr with hqr | hqr
    · exact Or.inr (by simpa only [← hqr] using hpq)
    · apply Or.inr
      apply (h.horizontalLT_iff_orientation_signs p r).mpr
      have hpqSigns := (h.horizontalLT_iff_orientation_signs p q).mp hpq
      have hqrSigns := (h.horizontalLT_iff_orientation_signs q r).mp hqr
      exact ⟨fixed_anchor_orientation_trans outerLeft outerRight outerLeft
          p.1 q.1 r.1 (Or.inl rfl) (h.base_orientation_pos p)
          (h.base_orientation_pos q) (h.base_orientation_pos r)
          hpqSigns.1 hqrSigns.1,
        fixed_anchor_orientation_trans outerLeft outerRight outerRight
          p.1 q.1 r.1 (Or.inr rfl) (h.base_orientation_pos p)
          (h.base_orientation_pos q) (h.base_orientation_pos r)
          hpqSigns.2 hqrSigns.2⟩

private theorem vertical_horizontal_incompatible
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : p.1 ≠ q.1) :
    ¬ ((HMPTSpikeVerticalLE outerLeft outerRight p.1 q.1 ∨
          HMPTSpikeVerticalLE outerLeft outerRight q.1 p.1) ∧
        (HMPTSpikeHorizontalLE outerLeft outerRight p.1 q.1 ∨
          HMPTSpikeHorizontalLE outerLeft outerRight q.1 p.1)) := by
  rintro ⟨hvertical, hhorizontal⟩
  rcases hvertical with hvpq | hvqp <;>
    rcases hhorizontal with hhpq | hhqp
  · have hv := (h.verticalLE_iff_orientation_signs_of_ne p q hpq).mp hvpq
    have hh := (h.horizontalLE_iff_orientation_signs_of_ne p q hpq).mp hhpq
    linarith
  · have hv := (h.verticalLE_iff_orientation_signs_of_ne p q hpq).mp hvpq
    have hh := (h.horizontalLE_iff_orientation_signs_of_ne q p (Ne.symm hpq)).mp hhqp
    rw [orientation_swap_last outerLeft p.1 q.1,
      orientation_swap_last outerRight p.1 q.1] at hh
    linarith
  · have hv := (h.verticalLE_iff_orientation_signs_of_ne q p (Ne.symm hpq)).mp hvqp
    have hh := (h.horizontalLE_iff_orientation_signs_of_ne p q hpq).mp hhpq
    rw [orientation_swap_last outerLeft p.1 q.1,
      orientation_swap_last outerRight p.1 q.1] at hv
    linarith
  · have hv := (h.verticalLE_iff_orientation_signs_of_ne q p (Ne.symm hpq)).mp hvqp
    have hh := (h.horizontalLE_iff_orientation_signs_of_ne q p (Ne.symm hpq)).mp hhqp
    linarith

private theorem exhaustive_comparability
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : p.1 ≠ q.1) :
    (HMPTSpikeVerticalLE outerLeft outerRight p.1 q.1 ∨
        HMPTSpikeVerticalLE outerLeft outerRight q.1 p.1) ∨
      (HMPTSpikeHorizontalLE outerLeft outerRight p.1 q.1 ∨
        HMPTSpikeHorizontalLE outerLeft outerRight q.1 p.1) := by
  have hne := h.pair_orientations_ne p q hpq
  rcases lt_or_gt_of_ne hne.1 with hleftNeg | hleftPos <;>
    rcases lt_or_gt_of_ne hne.2 with hrightNeg | hrightPos
  · exact Or.inr (Or.inl
      ((h.horizontalLE_iff_orientation_signs_of_ne p q hpq).mpr
        ⟨hleftNeg, hrightNeg⟩))
  · apply Or.inl (Or.inr
      ((h.verticalLE_iff_orientation_signs_of_ne q p (Ne.symm hpq)).mpr ?_))
    rw [orientation_swap_last outerLeft p.1 q.1,
      orientation_swap_last outerRight p.1 q.1]
    exact ⟨by linarith, by linarith⟩
  · exact Or.inl (Or.inl
      ((h.verticalLE_iff_orientation_signs_of_ne p q hpq).mpr
        ⟨hleftPos, hrightNeg⟩))
  · apply Or.inr (Or.inr
      ((h.horizontalLE_iff_orientation_signs_of_ne q p (Ne.symm hpq)).mpr ?_))
    rw [orientation_swap_last outerLeft p.1 q.1,
      orientation_swap_last outerRight p.1 q.1]
    exact ⟨by linarith, by linarith⟩

/-- Observation 3.1 specialized directly to Euclidean support-region data. -/
theorem toHMPTSpikeOrderPair
    (h : SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s) :
    HMPTSpikeOrderPair outerLeft outerRight s := by
  refine {
    vertical_refl := ?_
    vertical_antisymm := ?_
    vertical_trans := ?_
    horizontal_refl := ?_
    horizontal_antisymm := ?_
    horizontal_trans := ?_
    exclusive_comparability := ?_
  }
  · intro p
    exact (hmptSpikeVerticalLE_iff_sukRegionLE_reverse
      outerLeft outerRight p.1 p.1).mpr
        (sukRegionLE_refl outerLeft outerRight p.1)
  · intro p q hpq hqp
    apply Subtype.ext
    apply sukRegionLE_antisymm_on (h.base_orientation_pos p)
      (h.base_orientation_pos q) (h.outer_pair_generalPosition p q)
    · exact (hmptSpikeVerticalLE_iff_sukRegionLE_reverse
        outerLeft outerRight q.1 p.1).mp hqp
    · exact (hmptSpikeVerticalLE_iff_sukRegionLE_reverse
        outerLeft outerRight p.1 q.1).mp hpq
  · intro p q r hpq hqr
    apply (hmptSpikeVerticalLE_iff_sukRegionLE_reverse
      outerLeft outerRight p.1 r.1).mpr
    exact sukRegionLE_trans outerLeft outerRight r.1 q.1 p.1
      ((hmptSpikeVerticalLE_iff_sukRegionLE_reverse
        outerLeft outerRight q.1 r.1).mp hqr)
      ((hmptSpikeVerticalLE_iff_sukRegionLE_reverse
        outerLeft outerRight p.1 q.1).mp hpq)
  · intro p
    exact Or.inl rfl
  · intro p q hpq hqp
    by_cases heq : p.1 = q.1
    · exact Subtype.ext heq
    · have hpqStrict := (h.horizontalLE_iff_orientation_signs_of_ne p q heq).mp hpq
      have hqpStrict :=
        (h.horizontalLE_iff_orientation_signs_of_ne q p (Ne.symm heq)).mp hqp
      rw [orientation_swap_last outerLeft p.1 q.1] at hqpStrict
      exfalso
      linarith
  · intro p q r hpq hqr
    exact h.horizontalLE_trans p q r hpq hqr
  · intro p q hpq
    have hpqValues : p.1 ≠ q.1 := by
      intro heq
      exact hpq (Subtype.ext heq)
    exact ⟨h.exhaustive_comparability p q hpqValues,
      h.vertical_horizontal_incompatible p q hpqValues⟩

end SukRegionGeometry

end

end ErdosSzekeres

end
