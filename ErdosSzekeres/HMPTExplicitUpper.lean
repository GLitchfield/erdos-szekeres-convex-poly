module

public import ErdosSzekeres.HMPTAsymptoticParameters
public import ErdosSzekeres.HMPTProductAggregation
public import ErdosSzekeres.PorValtrSupportProduct

@[expose] public section

/-!
# Explicit HMPT asymptotic upper bound

This file chooses the square-root scale in the finite HMPT aggregation theorem
and packages the resulting point-set forcing bound.
-/

namespace ErdosSzekeres

private theorem hmptAggregationExponent_le_scale_h6 (n : ℕ) :
    hmptAggregationExponent n (hmptAsymptoticScale n) ≤
      n + 17 * hmptAsymptoticScale n := by
  have hspec := hmptAsymptoticScale_spec n
  have hr : 0 < hmptAsymptoticScale n := by omega
  have hceil :
      (n * Nat.clog 2 n) ⌈/⌉ hmptAsymptoticScale n ≤
        hmptAsymptoticScale n := by
    apply (ceilDiv_le_iff_le_mul hr).2
    simpa only [Nat.pow_two] using hspec.2.1
  unfold hmptAggregationExponent
  omega

private theorem four_mul_le_two_pow_succ_h6 (r : ℕ) :
    4 * r ≤ 2 ^ (r + 1) := by
  have hmul : 2 * r ≤ 2 ^ r := Nat.mul_le_pow (by omega) r
  calc
    4 * r = 2 * (2 * r) := by ring
    _ ≤ 2 * 2 ^ r := Nat.mul_le_mul_left 2 hmul
    _ = 2 ^ (r + 1) := by simp [pow_succ, Nat.mul_comm]

private theorem hmptAggregateThreshold_le_scale_h6 (n : ℕ) :
    4 * hmptAsymptoticScale n +
        2 ^ (hmptAggregationExponent n (hmptAsymptoticScale n) + 1) ≤
      2 ^ (n + 32 * hmptAsymptoticScale n + 1) := by
  let r := hmptAsymptoticScale n
  have hr : 3 ≤ r := hmptAsymptoticScale_spec n |>.1
  have hE : hmptAggregationExponent n r ≤ n + 17 * r := by
    simpa only [r] using hmptAggregationExponent_le_scale_h6 n
  have hfour : 4 * r ≤ 2 ^ (n + 17 * r + 1) := by
    exact (four_mul_le_two_pow_succ_h6 r).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hpower :
      2 ^ (hmptAggregationExponent n r + 1) ≤
        2 ^ (n + 17 * r + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc
    4 * r + 2 ^ (hmptAggregationExponent n r + 1) ≤
        2 ^ (n + 17 * r + 1) + 2 ^ (n + 17 * r + 1) :=
      Nat.add_le_add hfour hpower
    _ = 2 ^ (n + 17 * r + 2) := by
      rw [show n + 17 * r + 2 = n + 17 * r + 1 + 1 by omega, pow_succ]
      omega
    _ ≤ 2 ^ (n + 32 * r + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)

private theorem porValtrSupportDenominator_lt_scale_h6 (n : ℕ) (hn : 3 ≤ n) :
    porValtrSupportDenominator (hmptAsymptoticScale n) <
      2 ^ (n + 32 * hmptAsymptoticScale n + 1) := by
  have hnpos : 0 < n := by omega
  simp only [porValtrSupportDenominator]
  apply Nat.pow_lt_pow_right (by omega)
  omega

/-- The H5 bound after the exact square-root parameter choice. -/
theorem hmpt_scale_upper (n : ℕ) (hn : 3 ≤ n) :
    ForcesConvexPolygon n
      (2 ^ (n + 32 * hmptAsymptoticScale n + 1)) := by
  intro P hcard hgp
  by_contra hno
  have hr : 3 ≤ hmptAsymptoticScale n :=
    hmptAsymptoticScale_spec n |>.1
  obtain ⟨h⟩ := exists_porValtrSupportProductData P
    (hmptAsymptoticScale n) hr
    ((porValtrSupportDenominator_lt_scale_h6 n hn).trans_le hcard) hgp
  have hlt := h.card_lt_hmptAggregation hr hgp hno
  have hlower :
      4 * hmptAsymptoticScale n +
          2 ^ (hmptAggregationExponent n (hmptAsymptoticScale n) + 1) ≤
        P.card :=
    (hmptAggregateThreshold_le_scale_h6 n).trans hcard
  exact (not_lt_of_ge hlower) hlt

/-- The explicit HMPT upper bound in published asymptotic form. -/
theorem hmpt_explicit_upper (n : ℕ) (hn : 3 ≤ n) :
    ForcesConvexPolygon n
      (2 ^ (n + 32 * Nat.sqrt (n * Nat.clog 2 n) + 128)) := by
  intro P hcard hgp
  apply hmpt_scale_upper n hn P _ hgp
  have hscale := hmptAsymptoticScale_spec n |>.2.2
  apply (Nat.pow_le_pow_right (by omega) (by omega)).trans hcard

end ErdosSzekeres
