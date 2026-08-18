module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Sym.Card

@[expose] public section

/-!
# Arithmetic for finite HMPT aggregation

This file packages the conservative exponent and the boundary-safe binomial
estimates used by the finite HMPT aggregation layer.
-/

namespace ErdosSzekeres

/-- The conservative exponent used by the finite HMPT aggregation layer. -/
def hmptAggregationExponent (n r : ℕ) : ℕ :=
  n + (n * Nat.clog 2 n) ⌈/⌉ r + 16 * r

/-- A conservative binomial bound that is valid at every natural boundary. -/
theorem choose_add_le_succ_pow (a b : ℕ) :
    Nat.choose (a + b) a ≤ (b + 1) ^ a := by
  calc
    Nat.choose (a + b) a =
        Fintype.card (Sym (Fin (b + 1)) a) := by
      rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      apply congrArg (fun n => Nat.choose n a)
      omega
    _ = Fintype.card (Sym.Sym' (Fin (b + 1)) a) :=
      Fintype.card_congr
        (Sym.symEquivSym' (α := Fin (b + 1)) (n := a))
    _ ≤ Fintype.card (List.Vector (Fin (b + 1)) a) := by
      exact Fintype.card_quotient_le
        (List.Vector.Perm.isSetoid (Fin (b + 1)) a)
    _ = (b + 1) ^ a := by simp

/-- The exact truncated-cardinality form consumed by H5. -/
theorem choose_sub_le_pow_sub (c d : ℕ) :
    Nat.choose (c + d - 2) (c - 1) ≤ d ^ (c - 1) := by
  by_cases hc0 : c = 0
  · subst c
    simp
  by_cases hc1 : c = 1
  · subst c
    simp
  have hc : 2 ≤ c := by omega
  by_cases hd0 : d = 0
  · subst d
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _
  by_cases hd1 : d = 1
  · subst d
    rw [show c + 1 - 2 = c - 1 by omega, Nat.choose_self, one_pow]
  have hd : 2 ≤ d := by omega
  have htop : c + d - 2 = (c - 1) + (d - 1) := by omega
  have hbase : d - 1 + 1 = d := by omega
  rw [htop]
  simpa only [hbase] using choose_add_le_succ_pow (c - 1) (d - 1)

end ErdosSzekeres
