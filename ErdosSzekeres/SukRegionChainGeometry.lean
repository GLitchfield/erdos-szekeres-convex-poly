module

public import ErdosSzekeres.SukRegionChainCupCap
public import ErdosSzekeres.TothValtrCapExtension

@[expose] public section

/-!
# Geometry and full-cap promotion for one Suk support region

This module derives the two-color semantics and transitivity used by the
finite Suk-region chain theorem from the actual open support-region signs.
It then promotes the theorem's anchored monochromatic chain to convex
position of the entire selected set together with its anchor.
-/

namespace ErdosSzekeres

noncomputable section

/-- Four consecutive cap anchors, with their complete local order type. -/
structure SukFourCapAnchors
    (outerLeft rightAnchor leftAnchor outerRight : Point 2) : Prop where
  orient012 : orientation outerLeft rightAnchor leftAnchor < 0
  orient013 : orientation outerLeft rightAnchor outerRight < 0
  orient023 : orientation outerLeft leftAnchor outerRight < 0
  orient123 : orientation rightAnchor leftAnchor outerRight < 0

/-- The raw geometric input for one Suk support region.  The color,
transitivity, and every convexity conclusion are deliberately absent. -/
structure SukRegionGeometry
    (outerLeft rightAnchor leftAnchor outerRight : Point 2)
    (s : Finset (Point 2)) : Prop where
  anchorsCap : SukFourCapAnchors
    outerLeft rightAnchor leftAnchor outerRight
  generalPosition : InGeneralPosition
    (insert outerLeft
      (insert rightAnchor (insert leftAnchor (insert outerRight s))))
  region : ∀ {p : Point 2}, p ∈ s →
    p ∈ SukSupportRegion outerLeft rightAnchor leftAnchor outerRight

/-- The exact source color: negative orientation is the right-anchor color. -/
def sukRegionGeometryColor {s : Finset (Point 2)}
    (p q r : ↥s) : Turn :=
  if orientation p.1 q.1 r.1 < 0 then Turn.right else Turn.left

/-- A selected set of the prescribed size whose full anchor extension is in
convex position. -/
def SukRegionHasFullAnchoredCap
    (anchor : Point 2) (s : Finset (Point 2)) (k : ℕ) : Prop :=
  ∃ selected : Finset (Point 2),
    selected ⊆ s ∧ selected.card = k ∧
      InConvexPosition (insert anchor selected)

theorem SukFiveCapAnchors.leftFour
    {x0 x1 x2 x3 x4 : Point 2}
    (h : SukFiveCapAnchors x0 x1 x2 x3 x4) :
    SukFourCapAnchors x0 x1 x2 x3 :=
  ⟨h.orient012, h.orient013, h.orient023, h.orient123⟩

theorem SukFiveCapAnchors.rightFour
    {x0 x1 x2 x3 x4 : Point 2}
    (h : SukFiveCapAnchors x0 x1 x2 x3 x4) :
    SukFourCapAnchors x1 x2 x3 x4 :=
  ⟨h.orient123, h.orient124, h.orient134, h.orient234⟩

/-- The rank-three Grassmann--Plücker identity for five affine points. -/
private theorem orientation_plucker (a b c d e : Point 2) :
    orientation a b c * orientation a d e -
      orientation a b d * orientation a c e +
      orientation a b e * orientation a c d = 0 := by
  simp only [orientation]
  ring

/-- Reversing all three arguments reverses orientation. -/
private theorem orientation_reverse (a b c : Point 2) :
    orientation c b a = -orientation a b c := by
  simp only [orientation]
  ring

private theorem support_base_orientation_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (habd : orientation a b d < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (habp : orientation a b p < 0)
    (hcdp : orientation c d p < 0) :
    0 < orientation a d p := by
  have hpluckerC := orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p, orientation_swap b c d] at hpluckerC
  have hcap : orientation c a p < 0 := by
    nlinarith
  have hacp : 0 < orientation a c p := by
    rw [orientation_swap a c p] at hcap
    linarith
  have hpluckerA := orientation_plucker a b c d p
  nlinarith

private theorem support_left_diagonal_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (hcdp : orientation c d p < 0) :
    0 < orientation a c p := by
  have hplucker := orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

private theorem support_right_diagonal_pos
    (b c d e p : Point 2)
    (hbcd : orientation b c d < 0)
    (hbce : orientation b c e < 0)
    (hcde : orientation c d e < 0)
    (hcdp : 0 < orientation c d p)
    (hbcp : orientation b c p < 0) :
    0 < orientation c e p := by
  have hplucker := orientation_plucker c b d e p
  rw [orientation_swap b c d, orientation_swap b c e,
    orientation_swap b c p] at hplucker
  nlinarith

private theorem orientation_nonneg_of_mem_triangle
    (a b c x y q : Point 2)
    (ha : 0 ≤ orientation x y a)
    (hb : 0 ≤ orientation x y b)
    (hc : 0 ≤ orientation x y c)
    (hq : q ∈ convexHull ℝ (triangle a b c)) :
    0 ≤ orientation x y q := by
  apply convexHull_min _ (convex_leftClosedHalfPlane x y) hq
  intro z hz
  change 0 ≤ orientation x y z
  simp only [triangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem support_signs
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) :
    0 < orientation rightAnchor leftAnchor p.1 ∧
      orientation outerLeft rightAnchor p.1 < 0 ∧
      orientation leftAnchor outerRight p.1 < 0 := by
  exact h.region p.property

theorem base_orientation_pos
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) :
    0 < orientation outerLeft outerRight p.1 := by
  rcases h.support_signs p with ⟨h12p, h01p, h23p⟩
  exact support_base_orientation_pos
    outerLeft rightAnchor leftAnchor outerRight p.1
    h.anchorsCap.orient012 h.anchorsCap.orient013
    h.anchorsCap.orient023 h.anchorsCap.orient123
    h12p h01p h23p

private theorem left_diagonal_pos
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) :
    0 < orientation outerLeft leftAnchor p.1 := by
  rcases h.support_signs p with ⟨h12p, -, h23p⟩
  exact support_left_diagonal_pos
    outerLeft rightAnchor leftAnchor outerRight p.1
    h.anchorsCap.orient012 h.anchorsCap.orient023
    h.anchorsCap.orient123 h12p h23p

private theorem right_diagonal_pos
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p : ↥s) :
    0 < orientation rightAnchor outerRight p.1 := by
  rcases h.support_signs p with ⟨h12p, h01p, -⟩
  exact support_right_diagonal_pos
    outerLeft rightAnchor leftAnchor outerRight p.1
    h.anchorsCap.orient012 h.anchorsCap.orient013
    h.anchorsCap.orient123 h12p h01p

private theorem ne_of_regionLT {p q : Point 2}
    (hpq : SukRegionLT outerLeft outerRight p q) : p ≠ q := by
  intro hpqEq
  subst q
  exact hpq.2 (sukRegionLE_refl outerLeft outerRight p)

private theorem regionLT_trans {p q r : Point 2}
    (hpq : SukRegionLT outerLeft outerRight p q)
    (hqr : SukRegionLT outerLeft outerRight q r) :
    SukRegionLT outerLeft outerRight p r := by
  refine ⟨sukRegionLE_trans outerLeft outerRight p q r hpq.1 hqr.1, ?_⟩
  intro hrp
  exact hqr.2 (sukRegionLE_trans outerLeft outerRight r p q hrp hpq.1)

theorem rightAnchor_pair_orientation_neg
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : SukRegionLT outerLeft outerRight p.1 q.1) :
    orientation rightAnchor p.1 q.1 < 0 := by
  rcases h.support_signs p with ⟨-, h01p, -⟩
  have h13p := h.right_diagonal_pos p
  have hweak : 0 ≤ orientation p.1 rightAnchor q.1 :=
    orientation_nonneg_of_mem_triangle
      outerLeft outerRight p.1 p.1 rightAnchor q.1
      (by rw [orientation_reverse]; linarith)
      (by simpa [orientation_cyclic'] using h13p.le)
      (by simp) hpq.1
  have hpqNe : p.1 ≠ q.1 := ne_of_regionLT hpq
  have hrightP : rightAnchor ≠ p.1 := by
    intro heq
    rw [← heq] at h01p
    simp at h01p
  have hrightQ : rightAnchor ≠ q.1 := by
    have h01q := (h.support_signs q).2.1
    intro heq
    rw [← heq] at h01q
    simp at h01q
  have hne : orientation rightAnchor p.1 q.1 ≠ 0 :=
    h.generalPosition (by simp) (by simp [p.property])
      (by simp [q.property]) hrightP hrightQ hpqNe
  have hneSwap : orientation p.1 rightAnchor q.1 ≠ 0 := by
    intro hzero
    apply hne
    rw [orientation_swap p.1 rightAnchor q.1, hzero]
    simp
  rw [orientation_swap p.1 rightAnchor q.1]
  exact neg_neg_of_pos (lt_of_le_of_ne hweak (Ne.symm hneSwap))

theorem leftAnchor_pair_orientation_pos
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : SukRegionLT outerLeft outerRight p.1 q.1) :
    0 < orientation leftAnchor p.1 q.1 := by
  rcases h.support_signs p with ⟨-, -, h23p⟩
  have h02p := h.left_diagonal_pos p
  have hweak : 0 ≤ orientation leftAnchor p.1 q.1 :=
    orientation_nonneg_of_mem_triangle
      outerLeft outerRight p.1 leftAnchor p.1 q.1
      (by simpa [orientation_cyclic] using h02p.le)
      (by rw [orientation_swap_last]; linarith)
      (by simp) hpq.1
  have hpqNe : p.1 ≠ q.1 := ne_of_regionLT hpq
  have hleftP : leftAnchor ≠ p.1 := by
    intro heq
    rw [← heq] at h23p
    simp at h23p
  have hleftQ : leftAnchor ≠ q.1 := by
    have h23q := (h.support_signs q).2.2
    intro heq
    rw [← heq] at h23q
    simp at h23q
  have hne : orientation leftAnchor p.1 q.1 ≠ 0 :=
    h.generalPosition (by simp) (by simp [p.property])
      (by simp [q.property]) hleftP hleftQ hpqNe
  exact lt_of_le_of_ne hweak (Ne.symm hne)

end SukRegionGeometry


private theorem fullAnchoredCap_of_embedding
    {s : Finset (Point 2)} {anchor : Point 2} {k : ℕ}
    (f : Fin k ↪ ↥s)
    (hgp : InGeneralPosition (insert anchor s))
    (htriple : ∀ (i j l : Fin k), i < j → j < l →
      InConvexPosition
        {anchor, (f i).1, (f j).1, (f l).1})
    (hfour : ∀ (i j l m : Fin k), i < j → j < l → l < m →
      InConvexPosition
        {(f i).1, (f j).1, (f l).1, (f m).1}) :
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
    have huEq :
        ({anchor, g (e 0), g (e 1), g (e 2)} :
          Finset (Point 2)) = u := by
      rw [show ({anchor, g (e 0), g (e 1), g (e 2)} :
          Finset (Point 2)) = insert anchor v by
        rw [← hpoints]]
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

private theorem anchored_convex_iff_orientation_neg
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

private theorem inConvexPosition_four_of_all_orientation_pos
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
    (by rw [orientation_reverse]; linarith)
  rw [show ({a, r, q, p} : Finset (Point 2)) = {a, p, q, r} by
    ext x
    simp [or_comm, or_left_comm]] at h
  exact h

private theorem anchored_convex_iff_orientation_pos
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
  · exact inConvexPosition_four_of_all_orientation_pos a p q r
      hapq hapr haqr

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem triple_orientation_ne
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : SukRegionLT outerLeft outerRight p.1 q.1)
    (hqr : SukRegionLT outerLeft outerRight q.1 r.1) :
    orientation p.1 q.1 r.1 ≠ 0 := by
  have hpqNe : p.1 ≠ q.1 := ne_of_regionLT hpq
  have hqrNe : q.1 ≠ r.1 := ne_of_regionLT hqr
  have hprNe : p.1 ≠ r.1 := ne_of_regionLT (regionLT_trans hpq hqr)
  exact h.generalPosition (by simp [p.property])
    (by simp [q.property]) (by simp [r.property])
    hpqNe hprNe hqrNe

theorem rightAnchor_convex_iff
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : SukRegionLT outerLeft outerRight p.1 q.1)
    (hqr : SukRegionLT outerLeft outerRight q.1 r.1) :
    InConvexPosition {rightAnchor, p.1, q.1, r.1} ↔
      orientation p.1 q.1 r.1 < 0 := by
  have hpr := regionLT_trans hpq hqr
  exact anchored_convex_iff_orientation_neg rightAnchor p.1 q.1 r.1
    (h.rightAnchor_pair_orientation_neg p q hpq)
    (h.rightAnchor_pair_orientation_neg p r hpr)
    (h.rightAnchor_pair_orientation_neg q r hqr)
    (h.triple_orientation_ne p q r hpq hqr)

theorem leftAnchor_convex_iff
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : SukRegionLT outerLeft outerRight p.1 q.1)
    (hqr : SukRegionLT outerLeft outerRight q.1 r.1) :
    InConvexPosition {leftAnchor, p.1, q.1, r.1} ↔
      0 < orientation p.1 q.1 r.1 := by
  have hpr := regionLT_trans hpq hqr
  exact anchored_convex_iff_orientation_pos leftAnchor p.1 q.1 r.1
    (h.leftAnchor_pair_orientation_pos p q hpq)
    (h.leftAnchor_pair_orientation_pos p r hpr)
    (h.leftAnchor_pair_orientation_pos q r hqr)
    (h.triple_orientation_ne p q r hpq hqr)

/-- The two anchor-extended convex quadruples are exhaustive and exclusive
on every increasing region triple. -/
theorem anchoredAlternatives_exhaustive_exclusive
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : SukRegionLT outerLeft outerRight p.1 q.1)
    (hqr : SukRegionLT outerLeft outerRight q.1 r.1) :
    (InConvexPosition {rightAnchor, p.1, q.1, r.1} ∨
      InConvexPosition {leftAnchor, p.1, q.1, r.1}) ∧
    ¬(InConvexPosition {rightAnchor, p.1, q.1, r.1} ∧
      InConvexPosition {leftAnchor, p.1, q.1, r.1}) := by
  have hne := h.triple_orientation_ne p q r hpq hqr
  rw [h.rightAnchor_convex_iff p q r hpq hqr,
    h.leftAnchor_convex_iff p q r hpq hqr]
  constructor
  · exact lt_or_gt_of_ne hne
  · rintro ⟨hneg, hpos⟩
    linarith

theorem geometryColor_right_iff
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : SukRegionLT outerLeft outerRight p.1 q.1)
    (hqr : SukRegionLT outerLeft outerRight q.1 r.1) :
    sukRegionGeometryColor p q r = Turn.right ↔
      InConvexPosition {rightAnchor, p.1, q.1, r.1} := by
  rw [h.rightAnchor_convex_iff p q r hpq hqr]
  simp [sukRegionGeometryColor]

theorem geometryColor_left_iff
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : SukRegionLT outerLeft outerRight p.1 q.1)
    (hqr : SukRegionLT outerLeft outerRight q.1 r.1) :
    sukRegionGeometryColor p q r = Turn.left ↔
      InConvexPosition {leftAnchor, p.1, q.1, r.1} := by
  rw [h.leftAnchor_convex_iff p q r hpq hqr]
  have hne := h.triple_orientation_ne p q r hpq hqr
  simp only [sukRegionGeometryColor]
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

/-- The exact color semantics required by the finite one-region chain
theorem, derived from raw support geometry. -/
theorem twoColorSemantics
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s) :
    SukRegionTwoColorSemantics rightAnchor leftAnchor outerLeft outerRight
      (sukRegionGeometryColor (s := s)) := by
  intro p q r hpq hqr
  exact ⟨h.geometryColor_right_iff p q r hpq hqr,
    h.geometryColor_left_iff p q r hpq hqr⟩

end SukRegionGeometry

/-- The projective chart used in the source's region-chain transitivity
argument. -/
private def sukRegionProjectiveChart
    (outerLeft rightAnchor outerRight p : Point 2) : Point 2 :=
  ![orientation outerLeft p rightAnchor /
      orientation outerLeft outerRight p,
    -orientation outerLeft outerRight rightAnchor /
      orientation outerLeft outerRight p]

private theorem sukRegionProjectiveChart_orientation
    (outerLeft rightAnchor outerRight p q r : Point 2)
    (hp : orientation outerLeft outerRight p ≠ 0)
    (hq : orientation outerLeft outerRight q ≠ 0)
    (hr : orientation outerLeft outerRight r ≠ 0) :
    orientation
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight p)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight q)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight r) =
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

private theorem sukRegionProjectiveChart_first_difference
    (outerLeft rightAnchor outerRight p q : Point 2)
    (hp : orientation outerLeft outerRight p ≠ 0)
    (hq : orientation outerLeft outerRight q ≠ 0) :
    (sukRegionProjectiveChart outerLeft rightAnchor outerRight q) 0 -
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight p) 0 =
      orientation outerLeft outerRight rightAnchor *
          orientation p outerLeft q /
        (orientation outerLeft outerRight p *
          orientation outerLeft outerRight q) := by
  simp only [sukRegionProjectiveChart, Matrix.cons_val_zero]
  field_simp
  simp only [orientation]
  ring

private theorem orientation_transitive_of_firstCoord_lt_pos
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

private theorem orientation_transitive_of_firstCoord_lt_neg
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

private theorem sukRegionProjectiveChart_orientation_pos_iff
    (outerLeft rightAnchor outerRight p q r : Point 2)
    (hanchor : 0 < orientation outerLeft outerRight rightAnchor)
    (hp : 0 < orientation outerLeft outerRight p)
    (hq : 0 < orientation outerLeft outerRight q)
    (hr : 0 < orientation outerLeft outerRight r) :
    0 < orientation
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight p)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight q)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight r) ↔
      0 < orientation p q r := by
  rw [sukRegionProjectiveChart_orientation outerLeft rightAnchor outerRight
    p q r (ne_of_gt hp) (ne_of_gt hq) (ne_of_gt hr)]
  have hfactor : 0 < orientation outerLeft outerRight rightAnchor ^ 2 /
      (orientation outerLeft outerRight p *
        orientation outerLeft outerRight q *
        orientation outerLeft outerRight r) :=
    div_pos (sq_pos_of_pos hanchor) (mul_pos (mul_pos hp hq) hr)
  exact mul_pos_iff_of_pos_left hfactor

private theorem sukRegionProjectiveChart_orientation_neg_iff
    (outerLeft rightAnchor outerRight p q r : Point 2)
    (hanchor : 0 < orientation outerLeft outerRight rightAnchor)
    (hp : 0 < orientation outerLeft outerRight p)
    (hq : 0 < orientation outerLeft outerRight q)
    (hr : 0 < orientation outerLeft outerRight r) :
    orientation
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight p)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight q)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight r) < 0 ↔
      orientation p q r < 0 := by
  rw [sukRegionProjectiveChart_orientation outerLeft rightAnchor outerRight
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

private theorem geometryColor_eq_right_iff
    {s : Finset (Point 2)} (p q r : ↥s) :
    sukRegionGeometryColor p q r = Turn.right ↔
      orientation p.1 q.1 r.1 < 0 := by
  simp [sukRegionGeometryColor]

private theorem geometryColor_eq_left_iff_of_ne
    {s : Finset (Point 2)} (p q r : ↥s)
    (hne : orientation p.1 q.1 r.1 ≠ 0) :
    sukRegionGeometryColor p q r = Turn.left ↔
      0 < orientation p.1 q.1 r.1 := by
  simp only [sukRegionGeometryColor]
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

private theorem chart_first_lt
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s) (hpq : SukRegionLT outerLeft outerRight p.1 q.1) :
    (sukRegionProjectiveChart outerLeft rightAnchor outerRight p.1) 0 <
      (sukRegionProjectiveChart outerLeft rightAnchor outerRight q.1) 0 := by
  have hp := h.base_orientation_pos p
  have hq := h.base_orientation_pos q
  have hinside :=
    (mem_convexHull_triangle_iff_of_orientation_pos
      outerLeft outerRight p.1 q.1 hp).mp hpq.1
  have hpqNe : p.1 ≠ q.1 := ne_of_regionLT hpq
  have houterP : outerLeft ≠ p.1 := by
    have h01p := (h.support_signs p).2.1
    intro heq
    rw [← heq] at h01p
    simp at h01p
  have houterQ : outerLeft ≠ q.1 := by
    have h01q := (h.support_signs q).2.1
    intro heq
    rw [← heq] at h01q
    simp at h01q
  have hpAqNe : orientation p.1 outerLeft q.1 ≠ 0 :=
    h.generalPosition (by simp [p.property]) (by simp)
      (by simp [q.property]) houterP.symm hpqNe houterQ
  have hpAq : 0 < orientation p.1 outerLeft q.1 :=
    lt_of_le_of_ne hinside.2.2 (Ne.symm hpAqNe)
  have hanchor : 0 < orientation outerLeft outerRight rightAnchor := by
    rw [orientation_swap_last]
    linarith [h.anchorsCap.orient013]
  have hdiff : 0 <
      (sukRegionProjectiveChart outerLeft rightAnchor outerRight q.1) 0 -
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight p.1) 0 := by
    rw [sukRegionProjectiveChart_first_difference
      outerLeft rightAnchor outerRight p.1 q.1 (ne_of_gt hp) (ne_of_gt hq)]
    exact div_pos (mul_pos hanchor hpAq) (mul_pos hp hq)
  linarith

/-- Raw support geometry produces the source's transitive two-coloring. -/
theorem transitiveTwoColoring
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s) :
    SukRegionTransitiveTwoColoring outerLeft outerRight
      (sukRegionGeometryColor (s := s)) := by
  intro p q r t hpq hqr hrt c hpqr hqrt
  have hp := h.base_orientation_pos p
  have hq := h.base_orientation_pos q
  have hr := h.base_orientation_pos r
  have ht := h.base_orientation_pos t
  have hanchor : 0 < orientation outerLeft outerRight rightAnchor := by
    rw [orientation_swap_last]
    linarith [h.anchorsCap.orient013]
  have hpqX := h.chart_first_lt p q hpq
  have hqrX := h.chart_first_lt q r hqr
  have hrtX := h.chart_first_lt r t hrt
  have hpqrNe := h.triple_orientation_ne p q r hpq hqr
  have hqrtNe := h.triple_orientation_ne q r t hqr hrt
  have hpqtNe := h.triple_orientation_ne p q t hpq
    (regionLT_trans hqr hrt)
  have hprtNe := h.triple_orientation_ne p r t
    (regionLT_trans hpq hqr) hrt
  cases c with
  | left =>
      have hpqrPos :=
        (geometryColor_eq_left_iff_of_ne p q r hpqrNe).mp hpqr
      have hqrtPos :=
        (geometryColor_eq_left_iff_of_ne q r t hqrtNe).mp hqrt
      have hchartPqr :=
        (sukRegionProjectiveChart_orientation_pos_iff
          outerLeft rightAnchor outerRight p.1 q.1 r.1
          hanchor hp hq hr).2 hpqrPos
      have hchartQrt :=
        (sukRegionProjectiveChart_orientation_pos_iff
          outerLeft rightAnchor outerRight q.1 r.1 t.1
          hanchor hq hr ht).2 hqrtPos
      have hout := orientation_transitive_of_firstCoord_lt_pos
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight p.1)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight q.1)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight r.1)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight t.1)
        hpqX hqrX hrtX hchartPqr hchartQrt
      have hpqtPos :=
        (sukRegionProjectiveChart_orientation_pos_iff
          outerLeft rightAnchor outerRight p.1 q.1 t.1
          hanchor hp hq ht).1 hout.1
      have hprtPos :=
        (sukRegionProjectiveChart_orientation_pos_iff
          outerLeft rightAnchor outerRight p.1 r.1 t.1
          hanchor hp hr ht).1 hout.2
      exact ⟨(geometryColor_eq_left_iff_of_ne p q t hpqtNe).2 hpqtPos,
        (geometryColor_eq_left_iff_of_ne p r t hprtNe).2 hprtPos⟩
  | right =>
      have hpqrNeg := (geometryColor_eq_right_iff p q r).mp hpqr
      have hqrtNeg := (geometryColor_eq_right_iff q r t).mp hqrt
      have hchartPqr :=
        (sukRegionProjectiveChart_orientation_neg_iff
          outerLeft rightAnchor outerRight p.1 q.1 r.1
          hanchor hp hq hr).2 hpqrNeg
      have hchartQrt :=
        (sukRegionProjectiveChart_orientation_neg_iff
          outerLeft rightAnchor outerRight q.1 r.1 t.1
          hanchor hq hr ht).2 hqrtNeg
      have hout := orientation_transitive_of_firstCoord_lt_neg
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight p.1)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight q.1)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight r.1)
        (sukRegionProjectiveChart outerLeft rightAnchor outerRight t.1)
        hpqX hqrX hrtX hchartPqr hchartQrt
      have hpqtNeg :=
        (sukRegionProjectiveChart_orientation_neg_iff
          outerLeft rightAnchor outerRight p.1 q.1 t.1
          hanchor hp hq ht).1 hout.1
      have hprtNeg :=
        (sukRegionProjectiveChart_orientation_neg_iff
          outerLeft rightAnchor outerRight p.1 r.1 t.1
          hanchor hp hr ht).1 hout.2
      exact ⟨(geometryColor_eq_right_iff p q t).2 hpqtNeg,
        (geometryColor_eq_right_iff p r t).2 hprtNeg⟩

end SukRegionGeometry

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem right_orientation_of_chain
    (f : Fin k ↪ ↥s)
    (hchain : ∀ (i j l : Fin k), i < j → j < l →
      sukRegionGeometryColor (f i) (f j) (f l) = Turn.right ∧
        InConvexPosition
          {rightAnchor, (f i).1, (f j).1, (f l).1})
    (i j l : Fin k) (hij : i < j) (hjl : j < l) :
    orientation (f i).1 (f j).1 (f l).1 < 0 :=
  (geometryColor_eq_right_iff (f i) (f j) (f l)).mp
    (hchain i j l hij hjl).1

private theorem left_orientation_of_chain
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (f : Fin k ↪ ↥s)
    (horder : ∀ (i j : Fin k), i < j →
      SukRegionLT outerLeft outerRight (f i).1 (f j).1)
    (hchain : ∀ (i j l : Fin k), i < j → j < l →
      sukRegionGeometryColor (f i) (f j) (f l) = Turn.left ∧
        InConvexPosition
          {leftAnchor, (f i).1, (f j).1, (f l).1})
    (i j l : Fin k) (hij : i < j) (hjl : j < l) :
    0 < orientation (f i).1 (f j).1 (f l).1 := by
  have hne := h.triple_orientation_ne (f i) (f j) (f l)
    (horder i j hij) (horder j l hjl)
  exact (geometryColor_eq_left_iff_of_ne (f i) (f j) (f l) hne).mp
    (hchain i j l hij hjl).1

theorem fullAnchoredCap_of_rightChain
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    {k : ℕ}
    (hchain : SukRegionHasAnchoredColorChain outerLeft outerRight
      (sukRegionGeometryColor (s := s)) Turn.right rightAnchor k) :
    SukRegionHasFullAnchoredCap rightAnchor s k := by
  rcases hchain with ⟨f, horder, htriples⟩
  have hgp : InGeneralPosition (insert rightAnchor s) := by
    apply h.generalPosition.mono
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp
    · simp [hp]
  apply fullAnchoredCap_of_embedding f hgp
  · intro i j l hij hjl
    exact (htriples i j l hij hjl).2
  · intro i j l m hij hjl hlm
    apply inConvexPosition_four_of_all_orientation_neg
    · exact right_orientation_of_chain f htriples i j l hij hjl
    · exact right_orientation_of_chain f htriples i j m hij (hjl.trans hlm)
    · exact right_orientation_of_chain f htriples i l m
        (hij.trans hjl) hlm
    · exact right_orientation_of_chain f htriples j l m hjl hlm

theorem fullAnchoredCap_of_leftChain
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    {k : ℕ}
    (hchain : SukRegionHasAnchoredColorChain outerLeft outerRight
      (sukRegionGeometryColor (s := s)) Turn.left leftAnchor k) :
    SukRegionHasFullAnchoredCap leftAnchor s k := by
  rcases hchain with ⟨f, horder, htriples⟩
  have hgp : InGeneralPosition (insert leftAnchor s) := by
    apply h.generalPosition.mono
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp
    · simp [hp]
  apply fullAnchoredCap_of_embedding f hgp
  · intro i j l hij hjl
    exact (htriples i j l hij hjl).2
  · intro i j l m hij hjl hlm
    apply inConvexPosition_four_of_all_orientation_pos
    · exact h.left_orientation_of_chain f horder htriples i j l hij hjl
    · exact h.left_orientation_of_chain f horder htriples i j m
        hij (hjl.trans hlm)
    · exact h.left_orientation_of_chain f horder htriples i l m
        (hij.trans hjl) hlm
    · exact h.left_orientation_of_chain f horder htriples j l m hjl hlm

end SukRegionGeometry

/-- Raw one-region support geometry, together with totality of the existing
triangle-containment order, yields a full right- or left-anchor cap at the
exact finite cup/cap threshold. -/
theorem sukRegionGeometry_to_fullAnchoredCap
    (outerLeft rightAnchor leftAnchor outerRight : Point 2)
    (s : Finset (Point 2))
    (hgeometry : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (hchain : ∀ {p : Point 2}, p ∈ s →
      ∀ {q : Point 2}, q ∈ s → p ≠ q →
      SukRegionLE outerLeft outerRight p q ∨
        SukRegionLE outerLeft outerRight q p)
    (rightSize leftSize : ℕ)
    (hrightSize : 2 ≤ rightSize) (hleftSize : 2 ≤ leftSize)
    (hcard : Nat.choose (rightSize + leftSize - 4) (rightSize - 2) <
      s.card) :
    SukRegionHasFullAnchoredCap rightAnchor s rightSize ∨
      SukRegionHasFullAnchoredCap leftAnchor s leftSize := by
  have halt := sukRegionChain_twoColor_cup_or_cap
    outerLeft rightAnchor leftAnchor outerRight s
    (fun p hp ↦ hgeometry.base_orientation_pos ⟨p, hp⟩)
    hgeometry.generalPosition
    (by
      intro p hp q hq hpq
      exact hchain hp hq hpq)
    (sukRegionGeometryColor (s := s))
    hgeometry.transitiveTwoColoring hgeometry.twoColorSemantics
    rightSize leftSize hrightSize hleftSize hcard
  rcases halt with hright | hleft
  · exact Or.inl (hgeometry.fullAnchoredCap_of_rightChain hright)
  · exact Or.inr (hgeometry.fullAnchoredCap_of_leftChain hleft)

/-- Complementary full anchored chains in two adjacent support pools
instantiate only the open global adjacent-chain selection interface. -/
theorem sukAdjacentAnchoredChains_to_globalSelection
    (x0 x1 x2 x3 x4 : Point 2)
    (leftPool rightPool : Finset (Point 2))
    (leftSize rightSize : ℕ)
    (hpools : SukAdjacentChainPools
      x0 x1 x2 x3 x4 leftPool rightPool)
    (hleft : SukRegionHasAnchoredColorChain x0 x3
      (sukRegionGeometryColor (s := leftPool)) Turn.left x2 leftSize)
    (hright : SukRegionHasAnchoredColorChain x1 x4
      (sukRegionGeometryColor (s := rightPool)) Turn.right x2 rightSize) :
    SukGlobalAdjacentChainSelection
      x2 leftPool rightPool leftSize rightSize := by
  let hleftGeometry : SukRegionGeometry x0 x1 x2 x3 leftPool := {
    anchorsCap := hpools.anchorsCap.leftFour
    generalPosition := by
      apply hpools.generalPosition.mono
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_union] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl | hp
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
    region := by
      intro p hp
      exact hpools.leftRegion hp
  }
  let hrightGeometry : SukRegionGeometry x1 x2 x3 x4 rightPool := {
    anchorsCap := hpools.anchorsCap.rightFour
    generalPosition := by
      apply hpools.generalPosition.mono
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_union] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl | hp
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))
    region := by
      intro p hp
      exact hpools.rightRegion hp
  }
  rcases hleftGeometry.fullAnchoredCap_of_leftChain hleft with
    ⟨left, hleftSubset, hleftCard, hleftConvex⟩
  rcases hrightGeometry.fullAnchoredCap_of_rightChain hright with
    ⟨right, hrightSubset, hrightCard, hrightConvex⟩
  exact ⟨left, right, hleftSubset, hrightSubset,
    hleftCard, hrightCard, hleftConvex, hrightConvex⟩

end

end ErdosSzekeres

end
