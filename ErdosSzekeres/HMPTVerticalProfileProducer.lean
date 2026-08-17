module

public import ErdosSzekeres.HMPTSpikeOrderConsumer
public import ErdosSzekeres.HMPTSpikeOrderGeometry
public import ErdosSzekeres.HMPTVerticalChainDefs

@[expose] public section

/-!
# The local HMPT vertical profile

This file produces the transitive vertical triple coloring and the complete
local profile used by the HMPT recurrence from one raw Suk region.  The
orientation color, both maximum chains, both maximum outer-anchored
subchains, and the binomial estimate are all constructed internally.
-/

namespace ErdosSzekeres

noncomputable section

private theorem convexHull_triangle_subset_iff_regionLE_c2
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

private theorem hmptVerticalLE_iff_regionLE_reverse_c2
    (outerLeft outerRight p q : Point 2) :
    HMPTSpikeVerticalLE outerLeft outerRight p q ↔
      SukRegionLE outerLeft outerRight q p := by
  constructor
  · rintro (rfl | hpq)
    · exact sukRegionLE_refl outerLeft outerRight p
    · exact (convexHull_triangle_subset_iff_regionLE_c2
        outerLeft outerRight p q).mp hpq.2
  · intro hpq
    by_cases heq : p = q
    · exact Or.inl heq
    · exact Or.inr ⟨heq,
        (convexHull_triangle_subset_iff_regionLE_c2
          outerLeft outerRight p q).mpr hpq⟩

private theorem orientation_reverse_c2 (a b c : Point 2) :
    orientation c b a = -orientation a b c := by
  simp only [orientation]
  ring

private def oppositeTurn : Turn → Turn
  | Turn.left => Turn.right
  | Turn.right => Turn.left

private theorem oppositeTurn_injective : Function.Injective oppositeTurn := by
  intro a b hab
  cases a <;> cases b <;> simp [oppositeTurn] at hab ⊢

private theorem hmptVerticalTripleColor_right_iff
    {s : Finset (Point 2)} (p q r : ↥s) :
    hmptVerticalTripleColor p q r = Turn.right ↔
      orientation p.1 q.1 r.1 < 0 := by
  simp [hmptVerticalTripleColor]

private theorem hmptVerticalTripleColor_left_iff_of_ne
    {s : Finset (Point 2)} (p q r : ↥s)
    (hne : orientation p.1 q.1 r.1 ≠ 0) :
    hmptVerticalTripleColor p q r = Turn.left ↔
      0 < orientation p.1 q.1 r.1 := by
  simp only [hmptVerticalTripleColor]
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

private theorem hmptVerticalTripleColor_reverse
    {s : Finset (Point 2)} (p q r : ↥s)
    (hne : orientation p.1 q.1 r.1 ≠ 0) :
    hmptVerticalTripleColor r q p =
      oppositeTurn (hmptVerticalTripleColor p q r) := by
  unfold hmptVerticalTripleColor
  rw [orientation_reverse_c2 p.1 q.1 r.1]
  by_cases hneg : orientation p.1 q.1 r.1 < 0
  · have hreverse : ¬ -orientation p.1 q.1 r.1 < 0 := by
      linarith
    simp [hneg, hreverse, oppositeTurn]
  · have hpos : 0 < orientation p.1 q.1 r.1 :=
      lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hne)
    have hreverse : -orientation p.1 q.1 r.1 < 0 := by
      linarith
    simp [hneg, hreverse, oppositeTurn]

private theorem inConvexPosition_of_card_le_three_c2
    {u : Finset (Point 2)} (hgp : InGeneralPosition u)
    (hcard : u.card ≤ 3) : InConvexPosition u := by
  apply (inConvexPosition_iff_four_subsets u hgp).2
  intro t htu htcard
  have hle := Finset.card_le_card htu
  omega

private theorem inConvexPosition_four_of_all_orientation_pos_c2
    (a p q r : Point 2)
    (hapq : 0 < orientation a p q)
    (hapr : 0 < orientation a p r)
    (haqr : 0 < orientation a q r)
    (hpqr : 0 < orientation p q r) :
    InConvexPosition {a, p, q, r} := by
  have h := inConvexPosition_four_of_all_orientation_neg a r q p
    (by rw [orientation_swap_last]; linarith)
    (by rw [orientation_swap_last]; linarith)
    (by rw [orientation_swap_last]; linarith)
    (by rw [orientation_reverse_c2]; linarith)
  rw [show ({a, r, q, p} : Finset (Point 2)) = {a, p, q, r} by
    ext x
    simp [or_comm, or_left_comm]] at h
  exact h

private theorem anchored_convex_iff_orientation_neg_c2
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

private theorem anchored_convex_iff_orientation_pos_c2
    (a p q r : Point 2)
    (hapq : 0 < orientation a p q)
    (hapr : 0 < orientation a p r)
    (haqr : 0 < orientation a q r)
    (hpqr : orientation p q r ≠ 0) :
    InConvexPosition {a, p, q, r} ↔ 0 < orientation p q r := by
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
    · have hinside : q ∈ convexHull ℝ (triangle a p r) :=
        (mem_convexHull_triangle_iff_of_orientation_pos a p r q hapr).2
          ⟨hapq.le, by rw [orientation_swap_last]; linarith,
            by simpa [orientation_cyclic] using haqr.le⟩
      have houtside :=
        (inConvexPosition_four_iff_no_mem_triangle
          a p q r hap haq har hpq hpr hqr).1 hconvex
      exact (houtside.2.2.1 hinside).elim
    · exact hpqrPos
  · exact inConvexPosition_four_of_all_orientation_pos_c2 a p q r
      hapq hapr haqr

private theorem hmptChainPoints_mono_c2
    {s : Finset (Point 2)} {u v : Finset (↥s)} (huv : u ⊆ v) :
    hmptChainPoints u ⊆ hmptChainPoints v := by
  intro p hp
  rcases Finset.mem_map.mp hp with ⟨q, hqu, rfl⟩
  exact Finset.mem_map.mpr ⟨q, huv hqu, rfl⟩

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem restrict_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    {t : Finset (Point 2)} (ht : t ⊆ s) :
    SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight t := by
  refine {
    anchorsCap := h.anchorsCap
    generalPosition := ?_
    region := ?_
  }
  · apply h.generalPosition.mono
    intro p hp
    simp only [Finset.mem_insert] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl | hp
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (ht hp))))
  · intro p hp
    exact h.region (ht hp)

private theorem regionLT_ne_c2 {p q : Point 2}
    (hpq : SukRegionLT outerLeft outerRight p q) : p ≠ q := by
  intro heq
  subst q
  exact hpq.2 (sukRegionLE_refl outerLeft outerRight p)

private theorem regionLT_trans_c2 {p q r : Point 2}
    (hpq : SukRegionLT outerLeft outerRight p q)
    (hqr : SukRegionLT outerLeft outerRight q r) :
    SukRegionLT outerLeft outerRight p r := by
  refine ⟨sukRegionLE_trans outerLeft outerRight p q r hpq.1 hqr.1, ?_⟩
  intro hrp
  exact hqr.2 (sukRegionLE_trans outerLeft outerRight r p q hrp hpq.1)

private theorem triple_orientation_ne_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s) (hpq : p.1 ≠ q.1) (hpr : p.1 ≠ r.1)
    (hqr : q.1 ≠ r.1) : orientation p.1 q.1 r.1 ≠ 0 := by
  exact h.generalPosition (by simp [p.property])
    (by simp [q.property]) (by simp [r.property]) hpq hpr hqr

private theorem hmptVerticalLT_iff_regionLT_reverse_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) :
    HMPTSpikeVerticalLT outerLeft outerRight p.1 q.1 ↔
      SukRegionLT outerLeft outerRight q.1 p.1 := by
  constructor
  · rintro ⟨hpqNe, hpqSub⟩
    refine ⟨(convexHull_triangle_subset_iff_regionLE_c2
      outerLeft outerRight p.1 q.1).mp hpqSub, ?_⟩
    intro hpqRegion
    have hpqLE : HMPTSpikeVerticalLE outerLeft outerRight p.1 q.1 :=
      Or.inr ⟨hpqNe, hpqSub⟩
    have hqpLE : HMPTSpikeVerticalLE outerLeft outerRight q.1 p.1 :=
      (hmptVerticalLE_iff_regionLE_reverse_c2
        outerLeft outerRight q.1 p.1).mpr hpqRegion
    have heq := h.toHMPTSpikeOrderPair.vertical_antisymm p q hpqLE hqpLE
    exact hpqNe (congrArg Subtype.val heq)
  · intro hqp
    refine ⟨?_, (convexHull_triangle_subset_iff_regionLE_c2
      outerLeft outerRight p.1 q.1).mpr hqp.1⟩
    intro hpq
    apply hqp.2
    rw [hpq]
    exact sukRegionLE_refl outerLeft outerRight q.1

private theorem outerLeft_ne_point_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) : outerLeft ≠ p.1 := by
  intro heq
  have hp := h.base_orientation_pos p
  rw [heq] at hp
  simp at hp

private theorem outerRight_ne_point_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) : outerRight ≠ p.1 := by
  intro heq
  have hp := h.base_orientation_pos p
  rw [heq] at hp
  simp at hp

private theorem outerLeft_pair_orientation_neg_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : SukRegionLT outerLeft outerRight p.1 q.1) :
    orientation outerLeft p.1 q.1 < 0 := by
  have hinside := (mem_convexHull_triangle_iff_of_orientation_pos
    outerLeft outerRight p.1 q.1 (h.base_orientation_pos p)).mp hpq.1
  have hweak : orientation outerLeft p.1 q.1 ≤ 0 := by
    have hlast := hinside.2.2
    rw [← orientation_cyclic p.1 outerLeft q.1,
      orientation_swap_last outerLeft p.1 q.1] at hlast
    linarith
  have hne : orientation outerLeft p.1 q.1 ≠ 0 :=
    h.generalPosition (by simp) (by simp [p.property])
      (by simp [q.property]) (h.outerLeft_ne_point_c2 p)
      (h.outerLeft_ne_point_c2 q) (regionLT_ne_c2 hpq)
  exact lt_of_le_of_ne hweak hne

private theorem outerRight_pair_orientation_pos_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : SukRegionLT outerLeft outerRight p.1 q.1) :
    0 < orientation outerRight p.1 q.1 := by
  have hinside := (mem_convexHull_triangle_iff_of_orientation_pos
    outerLeft outerRight p.1 q.1 (h.base_orientation_pos p)).mp hpq.1
  have hne : orientation outerRight p.1 q.1 ≠ 0 :=
    h.generalPosition (by simp) (by simp [p.property])
      (by simp [q.property]) (h.outerRight_ne_point_c2 p)
      (h.outerRight_ne_point_c2 q) (regionLT_ne_c2 hpq)
  exact lt_of_le_of_ne hinside.2.1 (Ne.symm hne)

private theorem outerLeft_convex_iff_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : SukRegionLT outerLeft outerRight p.1 q.1)
    (hqr : SukRegionLT outerLeft outerRight q.1 r.1) :
    InConvexPosition {outerLeft, p.1, q.1, r.1} ↔
      orientation p.1 q.1 r.1 < 0 := by
  have hpr := regionLT_trans_c2 hpq hqr
  exact anchored_convex_iff_orientation_neg_c2 outerLeft p.1 q.1 r.1
    (h.outerLeft_pair_orientation_neg_c2 p q hpq)
    (h.outerLeft_pair_orientation_neg_c2 p r hpr)
    (h.outerLeft_pair_orientation_neg_c2 q r hqr)
    (h.triple_orientation_ne_c2 p q r (regionLT_ne_c2 hpq)
      (regionLT_ne_c2 hpr) (regionLT_ne_c2 hqr))

private theorem outerRight_convex_iff_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : SukRegionLT outerLeft outerRight p.1 q.1)
    (hqr : SukRegionLT outerLeft outerRight q.1 r.1) :
    InConvexPosition {outerRight, p.1, q.1, r.1} ↔
      0 < orientation p.1 q.1 r.1 := by
  have hpr := regionLT_trans_c2 hpq hqr
  exact anchored_convex_iff_orientation_pos_c2 outerRight p.1 q.1 r.1
    (h.outerRight_pair_orientation_pos_c2 p q hpq)
    (h.outerRight_pair_orientation_pos_c2 p r hpr)
    (h.outerRight_pair_orientation_pos_c2 q r hqr)
    (h.triple_orientation_ne_c2 p q r (regionLT_ne_c2 hpq)
      (regionLT_ne_c2 hpr) (regionLT_ne_c2 hqr))

private theorem outer_twoColorSemantics_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s) :
    SukRegionTwoColorSemantics outerLeft outerRight outerLeft outerRight
      (hmptVerticalTripleColor (s := s)) := by
  intro p q r hpq hqr
  have hne := h.triple_orientation_ne_c2 p q r
    (regionLT_ne_c2 hpq)
    (regionLT_ne_c2 (regionLT_trans_c2 hpq hqr))
    (regionLT_ne_c2 hqr)
  constructor
  · rw [h.outerLeft_convex_iff_c2 p q r hpq hqr]
    exact hmptVerticalTripleColor_right_iff p q r
  · rw [h.outerRight_convex_iff_c2 p q r hpq hqr]
    exact hmptVerticalTripleColor_left_iff_of_ne p q r hne

/-- The raw orientation coloring is transitive in the strict HMPT vertical
direction. -/
theorem hmptVerticalTransitiveColoring
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s) :
    HMPTVerticalTransitiveColoring outerLeft outerRight
      (hmptVerticalTripleColor (s := s)) := by
  intro p q r t hpq hqr hrt c hpqr hqrt
  have hqp := (h.hmptVerticalLT_iff_regionLT_reverse_c2 p q).mp hpq
  have hrq := (h.hmptVerticalLT_iff_regionLT_reverse_c2 q r).mp hqr
  have htr := (h.hmptVerticalLT_iff_regionLT_reverse_c2 r t).mp hrt
  have hrp := regionLT_trans_c2 hrq hqp
  have htq := regionLT_trans_c2 htr hrq
  have htp := regionLT_trans_c2 htq hqp
  have hpqrNe := h.triple_orientation_ne_c2 p q r
    (regionLT_ne_c2 hqp).symm (regionLT_ne_c2 hrp).symm
    (regionLT_ne_c2 hrq).symm
  have hqrtNe := h.triple_orientation_ne_c2 q r t
    (regionLT_ne_c2 hrq).symm (regionLT_ne_c2 htq).symm
    (regionLT_ne_c2 htr).symm
  have hpqtNe := h.triple_orientation_ne_c2 p q t
    (regionLT_ne_c2 hqp).symm (regionLT_ne_c2 htp).symm
    (regionLT_ne_c2 htq).symm
  have hprtNe := h.triple_orientation_ne_c2 p r t
    (regionLT_ne_c2 hrp).symm (regionLT_ne_c2 htp).symm
    (regionLT_ne_c2 htr).symm
  have htrans : SukRegionTransitiveTwoColoring outerLeft outerRight
      (hmptVerticalTripleColor (s := s)) := by
    simpa only [hmptVerticalTripleColor, sukRegionGeometryColor] using
      h.transitiveTwoColoring
  have htrq : hmptVerticalTripleColor t r q = oppositeTurn c := by
    rw [hmptVerticalTripleColor_reverse q r t hqrtNe, hqrt]
  have hrqp : hmptVerticalTripleColor r q p = oppositeTurn c := by
    rw [hmptVerticalTripleColor_reverse p q r hpqrNe, hpqr]
  have hout := htrans t r q p htr hrq hqp (oppositeTurn c) htrq hrqp
  constructor
  · apply oppositeTurn_injective
    calc
      oppositeTurn (hmptVerticalTripleColor p q t) =
          hmptVerticalTripleColor t q p :=
        (hmptVerticalTripleColor_reverse p q t hpqtNe).symm
      _ = oppositeTurn c := hout.2
  · apply oppositeTurn_injective
    calc
      oppositeTurn (hmptVerticalTripleColor p r t) =
          hmptVerticalTripleColor t r p :=
        (hmptVerticalTripleColor_reverse p r t hprtNe).symm
      _ = oppositeTurn c := hout.1

end SukRegionGeometry

private theorem fullAnchoredCap_of_embedding_c2
    {s : Finset (Point 2)} {anchor : Point 2} {k : ℕ}
    (f : Fin k ↪ ↥s)
    (hgp : InGeneralPosition (insert anchor s))
    (htriple : ∀ (i j l : Fin k), i < j → j < l →
      InConvexPosition {anchor, (f i).1, (f j).1, (f l).1})
    (hfour : ∀ (i j l m : Fin k), i < j → j < l → l < m →
      InConvexPosition {(f i).1, (f j).1, (f l).1, (f m).1}) :
    SukRegionHasFullAnchoredCap anchor s k := by
  classical
  let g : Fin k → Point 2 := fun i ↦ (f i).1
  let selected : Finset (Point 2) := Finset.univ.image g
  have hgInjective : Function.Injective g := by
    intro i j hij
    apply f.injective
    apply Subtype.ext
    exact hij
  have hselectedSubset : selected ⊆ s := by
    intro p hp
    simp only [selected, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    exact (f i).property
  have hselectedCard : selected.card = k := by
    calc
      selected.card = (Finset.univ.image g).card := rfl
      _ = (Finset.univ : Finset (Fin k)).card :=
        Finset.card_image_of_injective Finset.univ hgInjective
      _ = k := Finset.card_fin k
  have hselectedGP : InGeneralPosition (insert anchor selected) := by
    apply hgp.mono
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp
    · exact Finset.mem_insert_of_mem (hselectedSubset hp)
  refine ⟨selected, hselectedSubset, hselectedCard, ?_⟩
  apply (inConvexPosition_iff_four_subsets
    (insert anchor selected) hselectedGP).2
  intro u hu hucard
  by_cases hau : anchor ∈ u
  · let v := u.erase anchor
    have hvsub : v ⊆ selected := by
      intro p hp
      have hpu : p ∈ u := (Finset.mem_erase.mp hp).2
      rcases Finset.mem_insert.mp (hu hpu) with hpa | hpselected
      · exact False.elim ((Finset.mem_erase.mp hp).1 hpa)
      · exact hpselected
    have hvcard : v.card = 3 := by
      rw [Finset.card_erase_of_mem hau]
      omega
    have hvimage : v ⊆ Finset.univ.image g := by
      simpa [selected] using hvsub
    obtain ⟨w, hw⟩ := Finset.subset_univ_image_iff.mp hvimage
    have hwcard : w.card = 3 := by
      calc
        w.card = (w.image g).card :=
          (Finset.card_image_of_injective w hgInjective).symm
        _ = v.card := congrArg Finset.card hw
        _ = 3 := hvcard
    let e : Fin 3 ↪o Fin k := w.orderEmbOfFin hwcard
    have h01 : e 0 < e 1 := e.strictMono (by decide)
    have h12 : e 1 < e 2 := e.strictMono (by decide)
    have hpoints : ({g (e 0), g (e 1), g (e 2)} :
        Finset (Point 2)) = v := by
      have hfin3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
        decide
      calc
        ({g (e 0), g (e 1), g (e 2)} : Finset (Point 2)) =
            Finset.univ.image (g ∘ e) := by
          rw [hfin3]
          simp
        _ = (Finset.univ.image e).image g := by
          rw [Finset.image_image]
        _ = w.image g := by
          rw [Finset.image_orderEmbOfFin_univ]
        _ = v := hw
    have huEq : ({anchor, g (e 0), g (e 1), g (e 2)} :
        Finset (Point 2)) = u := by
      rw [show ({anchor, g (e 0), g (e 1), g (e 2)} :
          Finset (Point 2)) = insert anchor v by rw [← hpoints]]
      exact Finset.insert_erase hau
    rw [← huEq]
    exact htriple (e 0) (e 1) (e 2) h01 h12
  · have husub : u ⊆ selected := by
      intro p hp
      rcases Finset.mem_insert.mp (hu hp) with hpa | hpselected
      · exact False.elim (hau (hpa ▸ hp))
      · exact hpselected
    have huimage : u ⊆ Finset.univ.image g := by
      simpa [selected] using husub
    obtain ⟨w, hw⟩ := Finset.subset_univ_image_iff.mp huimage
    have hwcard : w.card = 4 := by
      calc
        w.card = (w.image g).card :=
          (Finset.card_image_of_injective w hgInjective).symm
        _ = u.card := congrArg Finset.card hw
        _ = 4 := hucard
    let e : Fin 4 ↪o Fin k := w.orderEmbOfFin hwcard
    have h01 : e 0 < e 1 := e.strictMono (by decide)
    have h12 : e 1 < e 2 := e.strictMono (by decide)
    have h23 : e 2 < e 3 := e.strictMono (by decide)
    have hpoints : ({g (e 0), g (e 1), g (e 2), g (e 3)} :
        Finset (Point 2)) = u := by
      have hfin4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
        decide
      calc
        ({g (e 0), g (e 1), g (e 2), g (e 3)} :
            Finset (Point 2)) = Finset.univ.image (g ∘ e) := by
          rw [hfin4]
          simp
        _ = (Finset.univ.image e).image g := by
          rw [Finset.image_image]
        _ = w.image g := by
          rw [Finset.image_orderEmbOfFin_univ]
        _ = u := hw
    rw [← hpoints]
    exact hfour (e 0) (e 1) (e 2) (e 3) h01 h12 h23

private theorem exists_maximum_anchored_subchain_c2
    {s : Finset (Point 2)} (anchor : Point 2)
    (verticalChain : Finset (↥s)) :
    ∃ selected : Finset (↥s),
      HMPTMaximumAnchoredVerticalSubchain anchor verticalChain selected := by
  classical
  let candidates : Finset (Finset (↥s)) :=
    verticalChain.powerset.filter fun selected ↦
      InConvexPosition (insert anchor (hmptChainPoints selected))
  have hemptyConvex :
      InConvexPosition (insert anchor (hmptChainPoints (∅ : Finset (↥s)))) := by
    apply inConvexPosition_of_card_le_three_c2
    · intro a ha b hb c hc hab hac hbc
      simp only [hmptChainPoints, Finset.map_empty, Finset.insert_empty,
        Finset.mem_singleton] at ha hb hc
      subst a
      subst b
      exact (hab rfl).elim
    · simp [hmptChainPoints]
  have hempty : (∅ : Finset (↥s)) ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simp), hemptyConvex⟩
  obtain ⟨selected, hselected, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  have hselectedParts := Finset.mem_filter.mp hselected
  refine ⟨selected, ⟨Finset.mem_powerset.mp hselectedParts.1,
    hselectedParts.2⟩, ?_⟩
  intro other hother
  apply hmax other
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hother.1, hother.2⟩

private theorem hmptChainPoints_filter_eq_c2
    {s : Finset (Point 2)} (verticalChain : Finset (↥s))
    (selected : Finset (Point 2))
    (hselected : selected ⊆ hmptChainPoints verticalChain) :
    hmptChainPoints (verticalChain.filter fun p ↦ p.1 ∈ selected) = selected := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (Finset.mem_filter.mp hq).2
  · intro hp
    have hpChain := hselected hp
    rcases Finset.mem_map.mp hpChain with ⟨q, hq, rfl⟩
    exact Finset.mem_map.mpr
      ⟨q, Finset.mem_filter.mpr ⟨hq, hp⟩, rfl⟩

private theorem anchoredSubchain_of_fullCap_c2
    {s : Finset (Point 2)} {anchor : Point 2} {k : ℕ}
    (verticalChain : Finset (↥s))
    (hcap : SukRegionHasFullAnchoredCap anchor
      (hmptChainPoints verticalChain) k) :
    ∃ selected : Finset (↥s),
      HMPTAnchoredVerticalSubchain anchor verticalChain selected ∧
        selected.card = k := by
  rcases hcap with ⟨u, hu, hucard, huconvex⟩
  let selected : Finset (↥s) := verticalChain.filter fun p ↦ p.1 ∈ u
  have hpoints : hmptChainPoints selected = u :=
    hmptChainPoints_filter_eq_c2 verticalChain u hu
  refine ⟨selected, ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
  · simpa only [hpoints] using huconvex
  · calc
      selected.card = (hmptChainPoints selected).card :=
        (hmptChainPoints_card selected).symm
      _ = u.card := congrArg Finset.card hpoints
      _ = k := hucard

private theorem whole_anchored_of_card_le_two_c2
    {s : Finset (Point 2)} {anchor : Point 2}
    (verticalChain : Finset (↥s))
    (hgp : InGeneralPosition
      (insert anchor (hmptChainPoints verticalChain)))
    (hcard : verticalChain.card ≤ 2) :
    HMPTAnchoredVerticalSubchain anchor verticalChain verticalChain := by
  refine ⟨fun _ hp ↦ hp, ?_⟩
  apply inConvexPosition_of_card_le_three_c2 hgp
  calc
    (insert anchor (hmptChainPoints verticalChain)).card ≤
        (hmptChainPoints verticalChain).card + 1 := Finset.card_insert_le _ _
    _ = verticalChain.card + 1 := by rw [hmptChainPoints_card]
    _ ≤ 3 := by omega

private theorem two_le_maximum_anchored_card_c2
    {s : Finset (Point 2)} {anchor : Point 2}
    {verticalChain selected : Finset (↥s)}
    (hgp : InGeneralPosition
      (insert anchor (hmptChainPoints verticalChain)))
    (hverticalCard : 2 ≤ verticalChain.card)
    (hmax : HMPTMaximumAnchoredVerticalSubchain
      anchor verticalChain selected) :
    2 ≤ selected.card := by
  obtain ⟨pair, hpair, hpairCard⟩ :=
    Finset.exists_subset_card_eq hverticalCard
  have hpairGP : InGeneralPosition
      (insert anchor (hmptChainPoints pair)) := by
    apply hgp.mono
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp
    · exact Finset.mem_insert_of_mem (hmptChainPoints_mono_c2 hpair hp)
  have hpairAnchored :
      HMPTAnchoredVerticalSubchain anchor verticalChain pair := by
    refine ⟨hpair, ?_⟩
    apply inConvexPosition_of_card_le_three_c2 hpairGP
    calc
      (insert anchor (hmptChainPoints pair)).card ≤
          (hmptChainPoints pair).card + 1 := Finset.card_insert_le _ _
      _ = pair.card + 1 := by rw [hmptChainPoints_card]
      _ ≤ 3 := by omega
  have hbound := hmax.2 pair hpairAnchored
  omega

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem outerLeft_chain_generalPosition_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalChain : Finset (↥s)) :
    InGeneralPosition (insert outerLeft (hmptChainPoints verticalChain)) := by
  apply h.generalPosition.mono
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · simp
  · have hpS := hmptChainPoints_subset verticalChain hp
    simp [hpS]

private theorem outerRight_chain_generalPosition_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalChain : Finset (↥s)) :
    InGeneralPosition (insert outerRight (hmptChainPoints verticalChain)) := by
  apply h.generalPosition.mono
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · simp
  · have hpS := hmptChainPoints_subset verticalChain hp
    simp [hpS]

private theorem fullOuterLeftCap_of_chain_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    {k : ℕ}
    (hchain : SukRegionHasAnchoredColorChain outerLeft outerRight
      (hmptVerticalTripleColor (s := s)) Turn.right outerLeft k) :
    SukRegionHasFullAnchoredCap outerLeft s k := by
  rcases hchain with ⟨f, -, htriples⟩
  have hgp : InGeneralPosition (insert outerLeft s) := by
    apply h.generalPosition.mono
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp
    · simp [hp]
  apply fullAnchoredCap_of_embedding_c2 f hgp
  · intro i j l hij hjl
    exact (htriples i j l hij hjl).2
  · intro i j l m hij hjl hlm
    apply inConvexPosition_four_of_all_orientation_neg
    · exact (hmptVerticalTripleColor_right_iff (f i) (f j) (f l)).mp
        (htriples i j l hij hjl).1
    · exact (hmptVerticalTripleColor_right_iff (f i) (f j) (f m)).mp
        (htriples i j m hij (hjl.trans hlm)).1
    · exact (hmptVerticalTripleColor_right_iff (f i) (f l) (f m)).mp
        (htriples i l m (hij.trans hjl) hlm).1
    · exact (hmptVerticalTripleColor_right_iff (f j) (f l) (f m)).mp
        (htriples j l m hjl hlm).1

private theorem fullOuterRightCap_of_chain_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    {k : ℕ}
    (hchain : SukRegionHasAnchoredColorChain outerLeft outerRight
      (hmptVerticalTripleColor (s := s)) Turn.left outerRight k) :
    SukRegionHasFullAnchoredCap outerRight s k := by
  rcases hchain with ⟨f, horder, htriples⟩
  have hgp : InGeneralPosition (insert outerRight s) := by
    apply h.generalPosition.mono
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp
    · simp [hp]
  apply fullAnchoredCap_of_embedding_c2 f hgp
  · intro i j l hij hjl
    exact (htriples i j l hij hjl).2
  · intro i j l m hij hjl hlm
    have hpos : ∀ (a b c : Fin k), a < b → b < c →
        0 < orientation (f a).1 (f b).1 (f c).1 := by
      intro a b c hab hbc
      have hac := regionLT_trans_c2 (horder a b hab) (horder b c hbc)
      have hne := h.triple_orientation_ne_c2 (f a) (f b) (f c)
        (regionLT_ne_c2 (horder a b hab)) (regionLT_ne_c2 hac)
        (regionLT_ne_c2 (horder b c hbc))
      exact (hmptVerticalTripleColor_left_iff_of_ne
        (f a) (f b) (f c) hne).mp (htriples a b c hab hbc).1
    exact inConvexPosition_four_of_all_orientation_pos_c2
      (f i).1 (f j).1 (f l).1 (f m).1
      (hpos i j l hij hjl)
      (hpos i j m hij (hjl.trans hlm))
      (hpos i l m (hij.trans hjl) hlm)
      (hpos j l m hjl hlm)

private theorem region_total_on_hmpt_chain_c2
    (verticalChain : Finset (↥s))
    (hchain : IsChain
      (fun p q : ↥s ↦ HMPTSpikeVerticalLE
        outerLeft outerRight p.1 q.1)
      (verticalChain : Set (↥s))) :
    ∀ ⦃p⦄, p ∈ hmptChainPoints verticalChain →
      ∀ ⦃q⦄, q ∈ hmptChainPoints verticalChain → p ≠ q →
        SukRegionLE outerLeft outerRight p q ∨
          SukRegionLE outerLeft outerRight q p := by
  intro p hp q hq hpq
  rcases Finset.mem_map.mp hp with ⟨p', hp', rfl⟩
  rcases Finset.mem_map.mp hq with ⟨q', hq', rfl⟩
  have hpq' : p' ≠ q' := by
    intro heq
    exact hpq (congrArg Subtype.val heq)
  rcases hchain hp' hq' hpq' with hpqVertical | hqpVertical
  · exact Or.inr ((hmptVerticalLE_iff_regionLE_reverse_c2
      outerLeft outerRight p'.1 q'.1).mp hpqVertical)
  · exact Or.inl ((hmptVerticalLE_iff_regionLE_reverse_c2
      outerLeft outerRight q'.1 p'.1).mp hqpVertical)

private theorem recurrence_generalPosition_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s) :
    InGeneralPosition
      (insert outerLeft
        (insert outerLeft (insert outerRight (insert outerRight s)))) := by
  apply h.generalPosition.mono
  intro p hp
  simp only [Finset.mem_insert] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl | hp
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hp)))

private theorem verticalCard_le_choose_c2
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalChain leftChain rightChain : Finset (↥s))
    (hvertical : HMPTMaximumChain
      (fun p q : ↥s ↦ HMPTSpikeVerticalLE outerLeft outerRight p.1 q.1)
      verticalChain)
    (hleft : HMPTMaximumAnchoredVerticalSubchain
      outerLeft verticalChain leftChain)
    (hright : HMPTMaximumAnchoredVerticalSubchain
      outerRight verticalChain rightChain) :
    verticalChain.card ≤
      Nat.choose (leftChain.card + rightChain.card - 2)
        (leftChain.card - 1) := by
  classical
  by_cases hsmall : verticalChain.card ≤ 2
  · have hleftWhole := whole_anchored_of_card_le_two_c2 verticalChain
      (h.outerLeft_chain_generalPosition_c2 verticalChain) hsmall
    have hrightWhole := whole_anchored_of_card_le_two_c2 verticalChain
      (h.outerRight_chain_generalPosition_c2 verticalChain) hsmall
    have hvertical_le_left := hleft.2 verticalChain hleftWhole
    have hleft_le_vertical := Finset.card_le_card hleft.1.1
    have hvertical_le_right := hright.2 verticalChain hrightWhole
    have hright_le_vertical := Finset.card_le_card hright.1.1
    have hleftCard : leftChain.card = verticalChain.card := by omega
    have hrightCard : rightChain.card = verticalChain.card := by omega
    interval_cases hverticalCard : verticalChain.card <;>
      simp [hleftCard, hrightCard]
  · have hverticalLarge : 3 ≤ verticalChain.card := by omega
    have hleftTwo : 2 ≤ leftChain.card :=
      two_le_maximum_anchored_card_c2
        (h.outerLeft_chain_generalPosition_c2 verticalChain)
        (by omega) hleft
    have hrightTwo : 2 ≤ rightChain.card :=
      two_le_maximum_anchored_card_c2
        (h.outerRight_chain_generalPosition_c2 verticalChain)
        (by omega) hright
    by_contra hbound
    have hchooseLt :
        Nat.choose (leftChain.card + rightChain.card - 2)
            (leftChain.card - 1) < verticalChain.card := by
      omega
    let t := hmptChainPoints verticalChain
    have htSubset : t ⊆ s := hmptChainPoints_subset verticalChain
    let htGeometry : SukRegionGeometry
        outerLeft rightAnchor leftAnchor outerRight t := h.restrict_c2 htSubset
    have hside : ∀ p ∈ t, 0 < orientation outerLeft outerRight p := by
      intro p hp
      exact htGeometry.base_orientation_pos ⟨p, hp⟩
    have htransitive : SukRegionTransitiveTwoColoring outerLeft outerRight
        (hmptVerticalTripleColor (s := t)) := by
      simpa only [hmptVerticalTripleColor, sukRegionGeometryColor] using
        htGeometry.transitiveTwoColoring
    have hsemantics : SukRegionTwoColorSemantics
        outerLeft outerRight outerLeft outerRight
        (hmptVerticalTripleColor (s := t)) :=
      htGeometry.outer_twoColorSemantics_c2
    have hrecurrenceCard :
        Nat.choose
            ((leftChain.card + 1) + (rightChain.card + 1) - 4)
            ((leftChain.card + 1) - 2) < t.card := by
      rw [show (leftChain.card + 1) + (rightChain.card + 1) - 4 =
          leftChain.card + rightChain.card - 2 by omega]
      rw [show leftChain.card + 1 - 2 = leftChain.card - 1 by omega]
      rw [hmptChainPoints_card]
      exact hchooseLt
    have halt := sukRegionChain_twoColor_cup_or_cap
      outerLeft outerLeft outerRight outerRight t hside
      htGeometry.recurrence_generalPosition_c2
      (region_total_on_hmpt_chain_c2 verticalChain hvertical.1)
      (hmptVerticalTripleColor (s := t)) htransitive hsemantics
      (leftChain.card + 1) (rightChain.card + 1)
      (by omega) (by omega) hrecurrenceCard
    rcases halt with hleftBranch | hrightBranch
    · have hcap := htGeometry.fullOuterLeftCap_of_chain_c2 hleftBranch
      obtain ⟨other, hother, hotherCard⟩ :=
        anchoredSubchain_of_fullCap_c2 verticalChain hcap
      have hmax := hleft.2 other hother
      omega
    · have hcap := htGeometry.fullOuterRightCap_of_chain_c2 hrightBranch
      obtain ⟨other, hother, hotherCard⟩ :=
        anchoredSubchain_of_fullCap_c2 verticalChain hcap
      have hmax := hright.2 other hother
      omega

/-- A raw Suk region internally produces both maximum spike-order chains,
both maximum outer-anchored vertical subchains, and their exact recurrence
bound. -/
theorem exists_hmptVerticalProfile
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s) :
    Nonempty (HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s) := by
  classical
  obtain ⟨verticalChain, horizontalChain, hvertical, hhorizontal, hproduct⟩ :=
    h.toHMPTSpikeOrderPair.exists_maxChains_card_le_product
  obtain ⟨leftChain, hleft⟩ :=
    exists_maximum_anchored_subchain_c2 outerLeft verticalChain
  obtain ⟨rightChain, hright⟩ :=
    exists_maximum_anchored_subchain_c2 outerRight verticalChain
  exact ⟨{
    verticalChain := verticalChain
    horizontalChain := horizontalChain
    verticalMaximum := hvertical
    horizontalMaximum := hhorizontal
    poolCard_le_product := hproduct
    leftChain := leftChain
    rightChain := rightChain
    leftMaximum := hleft
    rightMaximum := hright
    verticalCard_le_choose :=
      h.verticalCard_le_choose_c2 verticalChain leftChain rightChain
        hvertical hleft hright
  }⟩

end SukRegionGeometry

end

end ErdosSzekeres

end
