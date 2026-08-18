module

public import ErdosSzekeres.HMPTAggregationArithmetic
public import ErdosSzekeres.HMPTCyclicHorizontalProfiles

@[expose] public section

/-!
# Finite HMPT product aggregation

This file combines the original-carrier support-product inequality with the
exact cyclic H2--H4 profile family.  All products and exponents remain in the
natural numbers, including their truncated boundary cases.
-/

namespace ErdosSzekeres

noncomputable section

open scoped BigOperators

private def hmptCyclicSuccEquiv_b5 {r : ℕ} (hr : 3 ≤ r) :
    Fin (2 * r) ≃ Fin (2 * r) :=
  finCycle ⟨1, by omega⟩

private theorem hmptCyclicSucc_eq_equiv_b5 {r : ℕ} (hr : 3 ≤ r)
    (i : Fin (2 * r)) :
    hmptCyclicSucc i = hmptCyclicSuccEquiv_b5 hr i := by
  apply Fin.ext
  rfl

private theorem hmpt_n_pos_b5 {P : Finset (Point 2)} {r n : ℕ}
    {h : PorValtrSupportProductData P r}
    (package : HMPTCyclicHorizontalProfilePackage h n)
    (hr : 3 ≤ r) :
    0 < n := by
  let i : Fin (2 * r) := ⟨0, by omega⟩
  have hi := package.outerCard_lt i
  omega

private theorem hmptVerticalExponentSum_le_b5
    {P : Finset (Point 2)} {r n : ℕ}
    {h : PorValtrSupportProductData P r}
    (package : HMPTCyclicHorizontalProfilePackage h n)
    (hr : 3 ≤ r) :
    (∑ i : Fin (2 * r),
        ((package.verticalProfile i).leftChain.card +
          (package.verticalProfile i).rightChain.card)) ≤
      (2 * r) * n := by
  have hsucc :
      (∑ i : Fin (2 * r),
          (package.verticalProfile (hmptCyclicSucc i)).leftChain.card) =
        ∑ i : Fin (2 * r),
          (package.verticalProfile i).leftChain.card := by
    simpa only [hmptCyclicSucc_eq_equiv_b5] using
      (hmptCyclicSuccEquiv_b5 hr).sum_comp
        (fun i ↦ (package.verticalProfile i).leftChain.card)
  calc
    (∑ i : Fin (2 * r),
        ((package.verticalProfile i).leftChain.card +
          (package.verticalProfile i).rightChain.card)) =
        (∑ i : Fin (2 * r),
          (package.verticalProfile i).rightChain.card) +
        ∑ i : Fin (2 * r),
          (package.verticalProfile i).leftChain.card := by
      simp only [Finset.sum_add_distrib]
      omega
    _ = ∑ i : Fin (2 * r),
        ((package.verticalProfile i).rightChain.card +
          (package.verticalProfile (hmptCyclicSucc i)).leftChain.card) := by
      rw [Finset.sum_add_distrib, hsucc]
    _ ≤ ∑ _i : Fin (2 * r), n := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_of_lt (package.adjacentCard_lt i)
    _ = (2 * r) * n := by simp

private theorem hmptVerticalProduct_le_b5
    {P : Finset (Point 2)} {r n : ℕ}
    {h : PorValtrSupportProductData P r}
    (package : HMPTCyclicHorizontalProfilePackage h n)
    (hr : 3 ≤ r) :
    (∏ i : Fin (2 * r),
        (package.verticalProfile i).verticalChain.card) ≤
      2 ^ ((2 * r) * n) := by
  calc
    (∏ i : Fin (2 * r),
        (package.verticalProfile i).verticalChain.card) ≤
        ∏ i : Fin (2 * r),
          2 ^ ((package.verticalProfile i).leftChain.card +
            (package.verticalProfile i).rightChain.card) := by
      apply Finset.prod_le_prod'
      intro i _
      calc
        (package.verticalProfile i).verticalChain.card ≤
            Nat.choose
              ((package.verticalProfile i).leftChain.card +
                (package.verticalProfile i).rightChain.card - 2)
              ((package.verticalProfile i).leftChain.card - 1) :=
          (package.verticalProfile i).verticalCard_le_choose
        _ ≤ 2 ^
            ((package.verticalProfile i).leftChain.card +
              (package.verticalProfile i).rightChain.card - 2) :=
          Nat.choose_le_two_pow _ _
        _ ≤ 2 ^
            ((package.verticalProfile i).leftChain.card +
              (package.verticalProfile i).rightChain.card) := by
          apply Nat.pow_le_pow_right
          · omega
          · omega
    _ = 2 ^ (∑ i : Fin (2 * r),
        ((package.verticalProfile i).leftChain.card +
          (package.verticalProfile i).rightChain.card)) := by
      exact Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ 2 ^ ((2 * r) * n) := by
      apply Nat.pow_le_pow_right
      · omega
      · exact hmptVerticalExponentSum_le_b5 package hr

private theorem hmptHorizontalProduct_le_b5
    {P : Finset (Point 2)} {r n : ℕ}
    {h : PorValtrSupportProductData P r}
    (package : HMPTCyclicHorizontalProfilePackage h n)
    (hr : 3 ≤ r) :
    (∏ i : Fin (2 * r),
        (package.verticalProfile i).horizontalChain.card) ≤
      n ^ (2 * n) := by
  have hn : 0 < n := hmpt_n_pos_b5 package hr
  calc
    (∏ i : Fin (2 * r),
        (package.verticalProfile i).horizontalChain.card) ≤
        ∏ i : Fin (2 * r),
          n ^ (package.horizontalProfile i).innerChain.card := by
      apply Finset.prod_le_prod'
      intro i _
      calc
        (package.verticalProfile i).horizontalChain.card ≤
            Nat.choose
              ((package.horizontalProfile i).innerChain.card +
                (package.horizontalProfile i).outerChain.card - 2)
              ((package.horizontalProfile i).innerChain.card - 1) :=
          (package.horizontalProfile i).horizontalCard_le_choose
        _ ≤ (package.horizontalProfile i).outerChain.card ^
            ((package.horizontalProfile i).innerChain.card - 1) :=
          choose_sub_le_pow_sub _ _
        _ ≤ n ^ ((package.horizontalProfile i).innerChain.card - 1) :=
          Nat.pow_le_pow_left
            (Nat.le_of_lt (package.outerCard_lt i)) _
        _ ≤ n ^ (package.horizontalProfile i).innerChain.card := by
          apply Nat.pow_le_pow_right hn
          exact Nat.sub_le _ _
    _ = n ^ (∑ i : Fin (2 * r),
        (package.horizontalProfile i).innerChain.card) := by
      exact Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ n ^ (2 * n) := by
      apply Nat.pow_le_pow_right hn
      exact Nat.le_of_lt package.totalInnerCard_lt

private theorem hmptCard_sub_anchor_le_b5
    {P : Finset (Point 2)} {r n : ℕ}
    {h : PorValtrSupportProductData P r}
    (package : HMPTCyclicHorizontalProfilePackage h n)
    (hr : 3 ≤ r) :
    P.card - 4 * r ≤ 2 ^ hmptAggregationExponent n r := by
  change P.card - 4 * r ≤
    2 ^ (n + (n * Nat.clog 2 n) ⌈/⌉ r + 16 * r)
  have hn : 0 < n := hmpt_n_pos_b5 package hr
  have hnClog : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by omega) n
  have hnPower : n ^ (2 * n) ≤ 2 ^ (2 * n * Nat.clog 2 n) := by
    calc
      n ^ (2 * n) ≤ (2 ^ Nat.clog 2 n) ^ (2 * n) :=
        Nat.pow_le_pow_left hnClog _
      _ = 2 ^ (Nat.clog 2 n * (2 * n)) :=
        (pow_mul 2 (Nat.clog 2 n) (2 * n)).symm
      _ = 2 ^ (2 * n * Nat.clog 2 n) := by
        congr 1
        ring
  have hpoolProduct :
      (∏ i : Fin (2 * r), (h.hmptPool i).card) ≤
        2 ^ ((2 * r) * n + 2 * n * Nat.clog 2 n) := by
    calc
      (∏ i : Fin (2 * r), (h.hmptPool i).card) ≤
          ∏ i : Fin (2 * r),
            (package.verticalProfile i).verticalChain.card *
              (package.verticalProfile i).horizontalChain.card := by
        apply Finset.prod_le_prod'
        intro i _
        exact (package.verticalProfile i).poolCard_le_product
      _ =
          (∏ i : Fin (2 * r),
            (package.verticalProfile i).verticalChain.card) *
          ∏ i : Fin (2 * r),
            (package.verticalProfile i).horizontalChain.card := by
        exact Finset.prod_mul_distrib
      _ ≤ 2 ^ ((2 * r) * n) * n ^ (2 * n) :=
        Nat.mul_le_mul (hmptVerticalProduct_le_b5 package hr)
          (hmptHorizontalProduct_le_b5 package hr)
      _ ≤ 2 ^ ((2 * r) * n) * 2 ^ (2 * n * Nat.clog 2 n) := by
        exact Nat.mul_le_mul_left _ hnPower
      _ = 2 ^ ((2 * r) * n + 2 * n * Nat.clog 2 n) := by
        rw [pow_add]
  have hsource :
      (P.card - 4 * r) ^ (2 * r) ≤
        porValtrSupportDenominator r ^ r *
          ∏ i : Fin (2 * r), (h.hmptPool i).card := by
    calc
      (P.card - 4 * r) ^ (2 * r) ≤
          porValtrSupportDenominator r ^ r *
            ∏ i ∈ Finset.range (2 * r), (h.sourcePool i).card :=
        h.productBound
      _ = porValtrSupportDenominator r ^ r *
          ∏ i : Fin (2 * r), (h.hmptPool i).card := by
        congr 1
        calc
          (∏ i ∈ Finset.range (2 * r), (h.sourcePool i).card) =
              ∏ i : Fin (2 * r), (h.sourcePool i.1).card :=
            (Fin.prod_univ_eq_prod_range
              (fun i ↦ (h.sourcePool i).card) (2 * r)).symm
          _ = ∏ i : Fin (2 * r), (h.hmptPool i).card := by rfl
  have hsourcePower :
      (P.card - 4 * r) ^ (2 * r) ≤
        2 ^ (32 * r * r + ((2 * r) * n +
          2 * n * Nat.clog 2 n)) := by
    calc
      (P.card - 4 * r) ^ (2 * r) ≤
          porValtrSupportDenominator r ^ r *
            ∏ i : Fin (2 * r), (h.hmptPool i).card := hsource
      _ ≤ porValtrSupportDenominator r ^ r *
          2 ^ ((2 * r) * n + 2 * n * Nat.clog 2 n) := by
        exact Nat.mul_le_mul_left _ hpoolProduct
      _ = 2 ^ (32 * r * r + ((2 * r) * n +
          2 * n * Nat.clog 2 n)) := by
        simp only [porValtrSupportDenominator, pow_mul, pow_add]
  have hrpos : 0 < r := by omega
  have hceil :
      n * Nat.clog 2 n ≤
        r * ((n * Nat.clog 2 n) ⌈/⌉ r) :=
    (ceilDiv_le_iff_le_mul hrpos).1 le_rfl
  have hexponent :
      32 * r * r + ((2 * r) * n + 2 * n * Nat.clog 2 n) ≤
        (n + (n * Nat.clog 2 n) ⌈/⌉ r + 16 * r) *
          (2 * r) := by
    calc
      32 * r * r + ((2 * r) * n + 2 * n * Nat.clog 2 n) =
          (2 * r) * n + 2 * (n * Nat.clog 2 n) + 32 * r * r := by
        ring
      _ ≤ (2 * r) * n +
          2 * (r * ((n * Nat.clog 2 n) ⌈/⌉ r)) +
          32 * r * r := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hceil) _) _
      _ = (n + (n * Nat.clog 2 n) ⌈/⌉ r + 16 * r) *
          (2 * r) := by ring
  have hrootPower :
      (P.card - 4 * r) ^ (2 * r) ≤
        (2 ^ (n + (n * Nat.clog 2 n) ⌈/⌉ r + 16 * r)) ^
          (2 * r) := by
    calc
      (P.card - 4 * r) ^ (2 * r) ≤
          2 ^ (32 * r * r + ((2 * r) * n +
            2 * n * Nat.clog 2 n)) := hsourcePower
      _ ≤ 2 ^ ((n + (n * Nat.clog 2 n) ⌈/⌉ r + 16 * r) *
          (2 * r)) := Nat.pow_le_pow_right (by omega) hexponent
      _ = (2 ^ (n + (n * Nat.clog 2 n) ⌈/⌉ r + 16 * r)) ^
          (2 * r) := by rw [pow_mul]
  exact (Nat.pow_le_pow_iff_left (by omega)).mp hrootPower

private theorem hmptStrict_of_sub_anchor_le_b5
    {P : Finset (Point 2)} {r E : ℕ}
    (hcore : P.card - 4 * r ≤ 2 ^ E) :
    P.card < 4 * r + 2 ^ (E + 1) := by
  have hpowerPositive : 0 < 2 ^ E := pow_pos (by omega) _
  have hpowerStrict : 2 ^ E < 2 ^ (E + 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  by_cases hsmall : P.card ≤ 4 * r
  · omega
  · have hrecover : P.card ≤ 4 * r + 2 ^ E := by omega
    omega

namespace HMPTCyclicHorizontalProfilePackage

/-- Aggregate the exact stored H2/H3 family with the source product bound. -/
theorem card_sub_anchor_le
    {P : Finset (Point 2)} {r n : ℕ}
    {h : PorValtrSupportProductData P r}
    (package : HMPTCyclicHorizontalProfilePackage h n)
    (hr : 3 ≤ r) :
    P.card - 4 * r ≤ 2 ^ hmptAggregationExponent n r := by
  exact hmptCard_sub_anchor_le_b5 package hr

end HMPTCyclicHorizontalProfilePackage

namespace PorValtrSupportProductData

/-- Strict conservative H5 bound under the absence of a convex target. -/
theorem card_lt_hmptAggregation
    {P : Finset (Point 2)} {r n : ℕ}
    (h : PorValtrSupportProductData P r)
    (hr : 3 ≤ r)
    (hgp : InGeneralPosition P)
    (hno : ¬ContainsConvexSubset P n) :
    P.card < 4 * r + 2 ^ (hmptAggregationExponent n r + 1) := by
  obtain ⟨package⟩ :=
    h.exists_hmptCyclicHorizontalProfilePackage hr hgp hno
  exact hmptStrict_of_sub_anchor_le_b5 (package.card_sub_anchor_le hr)

end PorValtrSupportProductData

end

end ErdosSzekeres
