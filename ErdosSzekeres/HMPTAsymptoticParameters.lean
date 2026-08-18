module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

/-!
# Natural parameters for the HMPT asymptotic endpoint

This file records the conservative square-root scale used to instantiate the
finite HMPT aggregation bound.
-/

namespace ErdosSzekeres

/-- The conservative square-root parameter used by the HMPT endpoint. -/
def hmptAsymptoticScale (n : ℕ) : ℕ :=
  max 3 (Nat.sqrt (n * Nat.clog 2 n) + 1)

/-- The exact square-root cover and removal facts used by H6. -/
theorem hmptAsymptoticScale_spec (n : ℕ) :
    3 ≤ hmptAsymptoticScale n ∧
      n * Nat.clog 2 n ≤ hmptAsymptoticScale n ^ 2 ∧
      hmptAsymptoticScale n ≤
        Nat.sqrt (n * Nat.clog 2 n) + 3 := by
  unfold hmptAsymptoticScale
  constructor
  · exact le_max_left _ _
  constructor
  · have hroot :
        n * Nat.clog 2 n ≤
          (Nat.sqrt (n * Nat.clog 2 n) + 1) ^ 2 := by
      exact Nat.le_of_lt (by
        simpa only [Nat.succ_eq_add_one] using
          Nat.lt_succ_sqrt' (n * Nat.clog 2 n))
    exact hroot.trans
      (Nat.pow_le_pow_left
        (le_max_right 3 (Nat.sqrt (n * Nat.clog 2 n) + 1)) 2)
  · apply max_le
    · omega
    · omega

end ErdosSzekeres
