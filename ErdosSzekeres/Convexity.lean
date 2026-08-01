import ErdosSzekeres.Presentation
import Mathlib.Analysis.Convex.Combination

/-!
# Convexity from orientation signs

This file begins the safety bridge from the left/right triple coloring back to
the project's geometric convex-hull predicate.  Its first result is the closed
triangle test: for a positively oriented triangle, a point is in its convex
hull exactly when it lies weakly to the left of all three directed edges.
-/

namespace ErdosSzekeres

noncomputable section

/-- The closed half-plane weakly to the left of the directed line `ab`. -/
def leftClosedHalfPlane (a b : Point 2) : Set (Point 2) :=
  {p | 0 ≤ orientation a b p}

/-- Orientation is affine in its third argument. -/
theorem orientation_affine_combo_right (a b p q : Point 2) (u v : ℝ)
    (huv : u + v = 1) :
    orientation a b (u • p + v • q) =
      u * orientation a b p + v * orientation a b q := by
  simp only [orientation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination
    (-(b 1 - a 1) * a 0 + (b 0 - a 0) * a 1) * huv

/-- A closed orientation half-plane is convex. -/
theorem convex_leftClosedHalfPlane (a b : Point 2) :
    Convex ℝ (leftClosedHalfPlane a b) := by
  intro p hp q hq u v hu hv huv
  change 0 ≤ orientation a b (u • p + v • q)
  rw [orientation_affine_combo_right a b p q u v huv]
  exact add_nonneg (mul_nonneg hu hp) (mul_nonneg hv hq)

theorem orientation_cyclic (a b c : Point 2) :
    orientation b c a = orientation a b c := by
  simp only [orientation]
  ring

theorem orientation_cyclic' (a b c : Point 2) :
    orientation c a b = orientation a b c := by
  rw [orientation_cyclic c a b, orientation_cyclic b c a]

@[simp] theorem orientation_same_first (a c : Point 2) : orientation a a c = 0 := by
  simp only [orientation]
  ring

@[simp] theorem orientation_same_last (a b : Point 2) : orientation a b b = 0 := by
  simp only [orientation]
  ring

@[simp] theorem orientation_first_eq_third (a b : Point 2) : orientation a b a = 0 := by
  simp only [orientation]
  ring

theorem orientation_swap_last (a b c : Point 2) :
    orientation a c b = -orientation a b c := by
  simp only [orientation]
  ring

/-- The triangle with vertices `a`, `b`, and `c`. -/
def triangle (a b c : Point 2) : Set (Point 2) :=
  {a, b, c}

private theorem triangle_subset_leftClosedHalfPlane_ab (a b c : Point 2)
    (habc : 0 ≤ orientation a b c) :
    triangle a b c ⊆ leftClosedHalfPlane a b := by
  intro p hp
  simp only [triangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · simp [leftClosedHalfPlane]
  · simp [leftClosedHalfPlane]
  · exact habc

private theorem triangle_subset_leftClosedHalfPlane_bc (a b c : Point 2)
    (habc : 0 ≤ orientation a b c) :
    triangle a b c ⊆ leftClosedHalfPlane b c := by
  intro p hp
  simp only [triangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · simpa [leftClosedHalfPlane, orientation_cyclic] using habc
  · simp [leftClosedHalfPlane]
  · simp [leftClosedHalfPlane]

private theorem triangle_subset_leftClosedHalfPlane_ca (a b c : Point 2)
    (habc : 0 ≤ orientation a b c) :
    triangle a b c ⊆ leftClosedHalfPlane c a := by
  intro p hp
  simp only [triangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · simp [leftClosedHalfPlane]
  · simpa [leftClosedHalfPlane, orientation_cyclic'] using habc
  · simp [leftClosedHalfPlane]

/-- Membership in a positively oriented triangle is exactly the three closed
left-half-plane inequalities. -/
theorem mem_convexHull_triangle_iff_of_orientation_pos (a b c p : Point 2)
    (habc : 0 < orientation a b c) :
    p ∈ convexHull ℝ (triangle a b c) ↔
      0 ≤ orientation a b p ∧
      0 ≤ orientation b c p ∧
      0 ≤ orientation c a p := by
  constructor
  · intro hp
    refine ⟨?_, ?_, ?_⟩
    · exact convexHull_min (triangle_subset_leftClosedHalfPlane_ab a b c habc.le)
        (convex_leftClosedHalfPlane a b) hp
    · exact convexHull_min (triangle_subset_leftClosedHalfPlane_bc a b c habc.le)
        (convex_leftClosedHalfPlane b c) hp
    · exact convexHull_min (triangle_subset_leftClosedHalfPlane_ca a b c habc.le)
        (convex_leftClosedHalfPlane c a) hp
  · rintro ⟨habp, hbcp, hcap⟩
    let D := orientation a b c
    let wa := orientation b c p / D
    let wb := orientation c a p / D
    let wc := orientation a b p / D
    let w : Point 2 → ℝ := fun x =>
      if x = a then wa else if x = b then wb else if x = c then wc else 0
    have hab : a ≠ b := by
      intro h
      have hz : orientation a b c = 0 := by simp [h]
      linarith
    have hac : a ≠ c := by
      intro h
      have hz : orientation a b c = 0 := by simp [h]
      linarith
    have hbc : b ≠ c := by
      intro h
      have hz : orientation a b c = 0 := by simp [h]
      linarith
    rw [show triangle a b c =
      (↑({a, b, c} : Finset (Point 2)) : Set (Point 2)) by
        ext x
        simp [triangle]]
    apply Finset.mem_convexHull'.2
    refine ⟨w, ?_, ?_, ?_⟩
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hy | hy | hy
      · subst y
        simp [w, wa]
        exact div_nonneg hbcp habc.le
      · subst y
        simp [w, wb, hab.symm]
        exact div_nonneg hcap habc.le
      · subst y
        simp [w, wc, hac.symm, hbc.symm]
        exact div_nonneg habp habc.le
    · simp [w, wa, wb, wc, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
      dsimp [D]
      field_simp [ne_of_gt habc]
      simp only [orientation]
      ring
    · rw [Finset.sum_insert (by simp [hab, hac]),
        Finset.sum_insert (by simp [hbc]), Finset.sum_singleton]
      simp only [w, if_pos, if_neg hab.symm, if_neg hac.symm, if_neg hbc.symm,
        wa, wb, wc]
      funext i
      fin_cases i <;>
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      all_goals
        dsimp [D]
        field_simp [ne_of_gt habc]
        simp only [orientation]
        ring

/-- The orientation-reversed form of the closed triangle test. -/
theorem mem_convexHull_triangle_iff_of_orientation_neg (a b c p : Point 2)
    (habc : orientation a b c < 0) :
    p ∈ convexHull ℝ (triangle a b c) ↔
      orientation a b p ≤ 0 ∧
      orientation b c p ≤ 0 ∧
      orientation c a p ≤ 0 := by
  have hacb : 0 < orientation a c b := by
    rw [orientation_swap_last]
    linarith
  rw [show triangle a b c = triangle a c b by
    ext x
    simp [triangle, or_comm]]
  rw [mem_convexHull_triangle_iff_of_orientation_pos a c b p hacb]
  rw [orientation_swap c a p, orientation_swap b c p, orientation_swap a b p]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;>
    exact ⟨by linarith, by linarith, by linarith⟩

/-- The purely sign-based predicate saying that `p` lies strictly inside the
nondegenerate triangle `abc`. -/
def InsideTriangleBySigns (a b c p : Point 2) : Prop :=
  (0 < orientation a b c ∧
      0 < orientation a b p ∧ 0 < orientation b c p ∧ 0 < orientation c a p) ∨
    (orientation a b c < 0 ∧
      orientation a b p < 0 ∧ orientation b c p < 0 ∧ orientation c a p < 0)

/-- For a point in general position with a nondegenerate triangle, convex-hull
membership is determined entirely by the four orientation signs. -/
theorem mem_convexHull_triangle_iff_insideTriangleBySigns (a b c p : Point 2)
    (habc : orientation a b c ≠ 0)
    (habp : orientation a b p ≠ 0)
    (hbcp : orientation b c p ≠ 0)
    (hcap : orientation c a p ≠ 0) :
    p ∈ convexHull ℝ (triangle a b c) ↔ InsideTriangleBySigns a b c p := by
  rcases lt_or_gt_of_ne habc with habc_neg | habc_pos
  · rw [mem_convexHull_triangle_iff_of_orientation_neg a b c p habc_neg]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      right
      exact ⟨habc_neg,
        lt_of_le_of_ne h₁ habp,
        lt_of_le_of_ne h₂ hbcp,
        lt_of_le_of_ne h₃ hcap⟩
    · rintro (⟨hpos, -⟩ | ⟨-, h₁, h₂, h₃⟩)
      · linarith
      · exact ⟨h₁.le, h₂.le, h₃.le⟩
  · rw [mem_convexHull_triangle_iff_of_orientation_pos a b c p habc_pos]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      left
      exact ⟨habc_pos,
        lt_of_le_of_ne h₁ (Ne.symm habp),
        lt_of_le_of_ne h₂ (Ne.symm hbcp),
        lt_of_le_of_ne h₃ (Ne.symm hcap)⟩
    · rintro (⟨-, h₁, h₂, h₃⟩ | ⟨hneg, -⟩)
      · exact ⟨h₁.le, h₂.le, h₃.le⟩
      · linarith

/-- For four distinct points, the project's convex-position definition says
exactly that no point belongs to the triangle spanned by the other three. -/
theorem inConvexPosition_four_iff_no_mem_triangle (a b c d : Point 2)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    InConvexPosition {a, b, c, d} ↔
      a ∉ convexHull ℝ (triangle b c d) ∧
      b ∉ convexHull ℝ (triangle a c d) ∧
      c ∉ convexHull ℝ (triangle a b d) ∧
      d ∉ convexHull ℝ (triangle a b c) := by
  have ha :
      (↑(({a, b, c, d} : Finset (Point 2)).erase a) : Set (Point 2)) = triangle b c d := by
    ext x
    simp [triangle]
    aesop
  have hb :
      (↑(({a, b, c, d} : Finset (Point 2)).erase b) : Set (Point 2)) = triangle a c d := by
    ext x
    simp [triangle]
    aesop
  have hc :
      (↑(({a, b, c, d} : Finset (Point 2)).erase c) : Set (Point 2)) = triangle a b d := by
    ext x
    simp [triangle]
    aesop
  have hd :
      (↑(({a, b, c, d} : Finset (Point 2)).erase d) : Set (Point 2)) = triangle a b c := by
    ext x
    simp [triangle]
    aesop
  unfold InConvexPosition
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  rw [ha, hb, hc, hd]

/-- Four points in general position are in convex position exactly when none
of the four corresponding orientation-sign predicates says that one point is
inside the triangle of the other three.  This is the first entirely
combinatorial convexity certificate. -/
theorem inConvexPosition_four_iff_orientation_signs (a b c d : Point 2)
    (hgp : InGeneralPosition {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    InConvexPosition {a, b, c, d} ↔
      ¬InsideTriangleBySigns b c d a ∧
      ¬InsideTriangleBySigns a c d b ∧
      ¬InsideTriangleBySigns a b d c ∧
      ¬InsideTriangleBySigns a b c d := by
  have gp : ∀ ⦃x y z : Point 2⦄, x ∈ ({a, b, c, d} : Finset (Point 2)) →
      y ∈ ({a, b, c, d} : Finset (Point 2)) →
      z ∈ ({a, b, c, d} : Finset (Point 2)) →
      x ≠ y → x ≠ z → y ≠ z → orientation x y z ≠ 0 := by
    intro x y z hx hy hz hxy hxz hyz
    exact hgp hx hy hz hxy hxz hyz
  rw [inConvexPosition_four_iff_no_mem_triangle a b c d hab hac had hbc hbd hcd]
  rw [mem_convexHull_triangle_iff_insideTriangleBySigns b c d a
      (gp (by simp) (by simp) (by simp) hbc hbd hcd)
      (gp (by simp) (by simp) (by simp) hbc hab.symm hac.symm)
      (gp (by simp) (by simp) (by simp) hcd hac.symm had.symm)
      (gp (by simp) (by simp) (by simp) hbd.symm had.symm hab.symm),
    mem_convexHull_triangle_iff_insideTriangleBySigns a c d b
      (gp (by simp) (by simp) (by simp) hac had hcd)
      (gp (by simp) (by simp) (by simp) hac hab hbc.symm)
      (gp (by simp) (by simp) (by simp) hcd hbc.symm hbd.symm)
      (gp (by simp) (by simp) (by simp) had.symm hbd.symm hab),
    mem_convexHull_triangle_iff_insideTriangleBySigns a b d c
      (gp (by simp) (by simp) (by simp) hab had hbd)
      (gp (by simp) (by simp) (by simp) hab hac hbc)
      (gp (by simp) (by simp) (by simp) hbd hbc hcd.symm)
      (gp (by simp) (by simp) (by simp) had.symm hcd.symm hac),
    mem_convexHull_triangle_iff_insideTriangleBySigns a b c d
      (gp (by simp) (by simp) (by simp) hab hac hbc)
      (gp (by simp) (by simp) (by simp) hab had hbd)
      (gp (by simp) (by simp) (by simp) hbc hbd hcd)
      (gp (by simp) (by simp) (by simp) hac.symm hcd had)]

end

end ErdosSzekeres
