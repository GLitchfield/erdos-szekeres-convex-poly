module

public import ErdosSzekeres.TothValtrFrame

@[expose] public section

/-!
# The explicit projective chart used by Tóth and Valtr

The affine line `y = -δ` is sent to the line at infinity by the fractional
map

`(x, y) ↦ (x / (y + δ), y / (y + δ))`.

This file records the determinant identity needed to use that map without an
unformalized appeal to projective geometry.  On the half-plane `-δ < y`, the
three denominators and `δ` are positive, so every orientation sign is
preserved.
-/

namespace ErdosSzekeres

/-- The affine-chart formula for the projective transformation that sends
`y = -δ` to the line at infinity. -/
noncomputable def tothValtrProjective (δ : ℝ) (p : Point 2) : Point 2 :=
  ![p 0 / (p 1 + δ), p 1 / (p 1 + δ)]

@[simp] theorem tothValtrProjective_apply_zero (δ : ℝ) (p : Point 2) :
    tothValtrProjective δ p 0 = p 0 / (p 1 + δ) := by
  simp [tothValtrProjective]

@[simp] theorem tothValtrProjective_apply_one (δ : ℝ) (p : Point 2) :
    tothValtrProjective δ p 1 = p 1 / (p 1 + δ) := by
  simp [tothValtrProjective]

@[simp] theorem tothValtrProjective_zero (δ : ℝ) :
    tothValtrProjective δ 0 = 0 := by
  funext i
  fin_cases i <;> simp

/-- The exact determinant identity for the explicit projective chart. -/
theorem orientation_tothValtrProjective
    (δ : ℝ) (a b c : Point 2)
    (ha : a 1 + δ ≠ 0) (hb : b 1 + δ ≠ 0) (hc : c 1 + δ ≠ 0) :
    orientation (tothValtrProjective δ a)
        (tothValtrProjective δ b) (tothValtrProjective δ c) =
      δ * orientation a b c /
        ((a 1 + δ) * (b 1 + δ) * (c 1 + δ)) := by
  simp only [orientation, tothValtrProjective_apply_zero,
    tothValtrProjective_apply_one]
  field_simp [ha, hb, hc]
  ring

/-- On the positive-denominator chart, the projective normalization preserves
the sign of every orientation. -/
theorem orientation_tothValtrProjective_pos_iff
    (δ : ℝ) (a b c : Point 2) (hδ : 0 < δ)
    (ha : 0 < a 1 + δ) (hb : 0 < b 1 + δ) (hc : 0 < c 1 + δ) :
    0 < orientation (tothValtrProjective δ a)
        (tothValtrProjective δ b) (tothValtrProjective δ c) ↔
      0 < orientation a b c := by
  rw [orientation_tothValtrProjective δ a b c
    (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)]
  have hden : 0 < (a 1 + δ) * (b 1 + δ) * (c 1 + δ) :=
    mul_pos (mul_pos ha hb) hc
  constructor
  · intro h
    rcases div_pos_iff.mp h with ⟨hnum, -⟩ | ⟨-, hdenNeg⟩
    · rcases mul_pos_iff.mp hnum with ⟨-, horientation⟩ | ⟨hδNeg, -⟩
      · exact horientation
      · linarith
    · linarith
  · intro horientation
    exact div_pos (mul_pos hδ horientation) hden

/-- The negative orientation sign is preserved on the same chart. -/
theorem orientation_tothValtrProjective_neg_iff
    (δ : ℝ) (a b c : Point 2) (hδ : 0 < δ)
    (ha : 0 < a 1 + δ) (hb : 0 < b 1 + δ) (hc : 0 < c 1 + δ) :
    orientation (tothValtrProjective δ a)
        (tothValtrProjective δ b) (tothValtrProjective δ c) < 0 ↔
      orientation a b c < 0 := by
  rw [orientation_tothValtrProjective δ a b c
    (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)]
  have hden : 0 < (a 1 + δ) * (b 1 + δ) * (c 1 + δ) :=
    mul_pos (mul_pos ha hb) hc
  constructor
  · intro h
    rcases div_neg_iff.mp h with ⟨-, hdenNeg⟩ | ⟨hnum, -⟩
    · linarith
    · rcases mul_neg_iff.mp hnum with ⟨-, horientation⟩ | ⟨hδNeg, -⟩
      · exact horientation
      · linarith
  · intro habc
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hδ habc) hden

/-- The chart is injective wherever its two denominators are positive and
`δ` is nonzero. -/
theorem tothValtrProjective_injective_of_pos_denominators
    (δ : ℝ) (a b : Point 2) (hδ : δ ≠ 0)
    (ha : 0 < a 1 + δ) (hb : 0 < b 1 + δ)
    (hmap : tothValtrProjective δ a = tothValtrProjective δ b) :
    a = b := by
  have hyMap := congrFun hmap 1
  simp only [tothValtrProjective_apply_one] at hyMap
  have hy : a 1 = b 1 := by
    field_simp [ne_of_gt ha, ne_of_gt hb] at hyMap
    have hproduct : δ * (a 1 - b 1) = 0 := by
      nlinarith [hyMap]
    rcases mul_eq_zero.mp hproduct with hzero | hdiff
    · exact (hδ hzero).elim
    · linarith
  have hxMap := congrFun hmap 0
  simp only [tothValtrProjective_apply_zero, hy] at hxMap
  have hx : a 0 = b 0 := by
    exact (div_left_inj' (ne_of_gt hb)).mp hxMap
  funext i
  fin_cases i
  · exact hx
  · exact hy

end ErdosSzekeres

end
