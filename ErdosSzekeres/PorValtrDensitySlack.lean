module

public import ErdosSzekeres.Basic

@[expose] public section

/-!
# Pór--Valtr minus-one density slack

This module proves the exact natural-number exponent comparison and absorbs the
one-point loss in the source-faithful Pór--Valtr interior-pool bound.
-/

namespace ErdosSzekeres

/-- The denominator in the source-faithful Pór--Valtr interior-pool bound. -/
def porValtrFineDenominator (k : ℕ) : ℕ := 2 ^ (32 * (k + 3))

/-- The coarser denominator used by Suk's later positive-fraction argument. -/
def sukCoarseDenominator (k : ℕ) : ℕ := 2 ^ (40 * k)

/-- From `k = 13` onward, Suk's coarse denominator is at least twice the
Pór--Valtr denominator. -/
theorem porValtrFine_twice_le_sukCoarse
    {k : ℕ} (hk : 13 ≤ k) :
    2 * porValtrFineDenominator k ≤ sukCoarseDenominator k := by
  calc
    2 * porValtrFineDenominator k = 2 ^ (32 * (k + 3) + 1) := by
      simpa only [porValtrFineDenominator, Nat.pow_succ] using
        (Nat.mul_comm 2 (2 ^ (32 * (k + 3))))
    _ ≤ 2 ^ (40 * k) := by
      apply Nat.pow_le_pow_right (by omega)
      omega
    _ = sukCoarseDenominator k := rfl

/-- A source-faithful pool of size `q` absorbs its missing boundary point once
the ambient set has at least twice the fine denominator. -/
theorem porValtrMinusOne_to_sukCoarseDensity
    {k N q : ℕ}
    (hk : 13 ≤ k)
    (hlarge : 2 * porValtrFineDenominator k ≤ N)
    (hsource : N ≤ porValtrFineDenominator k * (q + 1)) :
    N ≤ sukCoarseDenominator k * q := by
  have hFinePos : 0 < porValtrFineDenominator k := by
    simp [porValtrFineDenominator]
  have hq : 1 ≤ q := by
    by_contra hq
    have hqZero : q = 0 := by omega
    subst q
    simp only [zero_add, mul_one] at hsource
    omega
  have hqSucc : q + 1 ≤ 2 * q := by omega
  calc
    N ≤ porValtrFineDenominator k * (q + 1) := hsource
    _ ≤ porValtrFineDenominator k * (2 * q) :=
      Nat.mul_le_mul_left (porValtrFineDenominator k) hqSucc
    _ = (2 * porValtrFineDenominator k) * q := by
      rw [← Nat.mul_assoc, Nat.mul_comm (porValtrFineDenominator k) 2]
    _ ≤ sukCoarseDenominator k * q :=
      Nat.mul_le_mul_right q (porValtrFine_twice_le_sukCoarse hk)

end ErdosSzekeres

end
