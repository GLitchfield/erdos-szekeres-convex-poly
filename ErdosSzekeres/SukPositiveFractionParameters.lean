module

public import ErdosSzekeres.PorValtrDensitySlack
public import ErdosSzekeres.SukGlobalBranchConsumer
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# Rounding-safe parameters for Suk's positive-fraction argument

This module packages the natural-number inequalities used by the global
chain/antichain consumer.  The cubic scale hypotheses avoid an independent
real-ceiling comparison: all lengths and carry widths use exact ceiling
division in `Nat`.
-/

namespace ErdosSzekeres

noncomputable section

/-- The least natural scale whose cube is at least `n`. -/
noncomputable def sukCubeScale (n : Nat) : Nat :=
  Nat.find (show Exists fun s : Nat ↦ n ≤ s ^ 3 from
    ⟨n, Nat.le_pow (by omega)⟩)

/-- Half the scale, rounded upward. -/
def sukSeparatedCount (s : Nat) : Nat :=
  s ⌈/⌉ 2

/-- Number of consecutive raw pools consumed by the global branch theorem. -/
def sukPoolLength (s : Nat) : Nat :=
  (2 * sukSeparatedCount s - 1) * s

/-- Width of one carry block, rounded upward. -/
def sukCarryWidth (n s : Nat) : Nat :=
  n ⌈/⌉ s

/-- Cap size extracted from one carry block. -/
def sukLocalCapSize (n s : Nat) : Nat :=
  2 * sukCarryWidth n s

/-- Strict threshold for one chain run. -/
def sukChainThreshold (n s : Nat) : Nat :=
  2 ^ (n + sukCarryWidth n s - 4) + 1

/-- Strict threshold for one antichain member. -/
def sukAntichainThreshold (n s : Nat) : Nat :=
  Nat.choose (n + sukLocalCapSize n s - 4) (n - 2) + 1

/-- Exact ambient threshold needed by both the fine Pór--Valtr source and
the coarser Suk pool-cardinality consumer. -/
def sukPositiveFractionThreshold (n s : Nat) : Nat :=
  max
    (2 * porValtrFineDenominator (sukPoolLength s))
    (sukCoarseDenominator (sukPoolLength s) *
      ((sukChainThreshold n s - 1) *
        (sukAntichainThreshold n s - 1) + 1))

/-- The exact arithmetic fields used to instantiate the global finite Suk
consumer at the frozen rounding-safe parameters. -/
structure SukPositiveFractionParameters (n s : Nat) where
  poolLengthLower : 13 ≤ sukPoolLength s
  chainSizePositive : 1 ≤ sukChainThreshold n s
  antichainSizePositive : 1 ≤ sukAntichainThreshold n s
  separatedCountPositive : 1 ≤ sukSeparatedCount s
  scaleLower : 2 ≤ s
  poolLengthCovers :
    (2 * sukSeparatedCount s - 1) * s ≤ sukPoolLength s
  carryWidthLower : 2 ≤ sukCarryWidth n s
  finalDeficit : 2 ≤ n - ((s - 1) * sukCarryWidth n s)
  finalSize : n ≤ s * sukCarryWidth n s
  chainCard : ∀ u, u < s →
    Nat.choose (n + sukCarryWidth n s - 4)
        ((u + 1) * sukCarryWidth n s - 2) <
      sukChainThreshold n s
  localCapSizeLower : 2 ≤ sukLocalCapSize n s
  antichainThreshold :
    Nat.choose (n + sukLocalCapSize n s - 4) (n - 2) <
      sukAntichainThreshold n s
  antichainTotal :
    n ≤ sukSeparatedCount s * sukLocalCapSize n s
  fineThreshold :
    2 * porValtrFineDenominator (sukPoolLength s) ≤
      sukPositiveFractionThreshold n s
  coarseThreshold :
    sukCoarseDenominator (sukPoolLength s) *
        ((sukChainThreshold n s - 1) *
          (sukAntichainThreshold n s - 1) + 1) ≤
      sukPositiveFractionThreshold n s

private theorem sukSeparatedCount_cover (s : Nat) :
    s ≤ 2 * sukSeparatedCount s := by
  change s ≤ 2 * (s ⌈/⌉ 2)
  exact (ceilDiv_le_iff_le_mul
    (a := (2 : Nat)) (b := s) (c := s ⌈/⌉ 2) (by omega)).1 le_rfl

private theorem sukCarryWidth_cover (n s : Nat) (hs : 0 < s) :
    n ≤ s * sukCarryWidth n s := by
  change n ≤ s * (n ⌈/⌉ s)
  exact (ceilDiv_le_iff_le_mul
    (a := s) (b := n) (c := n ⌈/⌉ s) hs).1 le_rfl

private theorem suk_scale_sq_le_pred_cube (s : Nat) (hs : 5 ≤ s) :
    s ^ 2 ≤ (s - 1) ^ 3 := by
  have hsPred : 4 ≤ s - 1 := by omega
  have htail : 2 * (s - 1) + 1 ≤ (s - 1) * (s - 1) := by
    calc
      2 * (s - 1) + 1 ≤ 3 * (s - 1) := by omega
      _ ≤ (s - 1) * (s - 1) :=
        Nat.mul_le_mul_right (s - 1) (by omega)
  rw [show s = (s - 1) + 1 by omega]
  calc
    ((s - 1) + 1) ^ 2 =
        (s - 1) * (s - 1) + (2 * (s - 1) + 1) := by ring
    _ ≤ (s - 1) * (s - 1) + (s - 1) * (s - 1) :=
      Nat.add_le_add_left htail _
    _ = 2 * (s - 1) ^ 2 := by ring
    _ ≤ (s - 1) * (s - 1) ^ 2 :=
      Nat.mul_le_mul_right ((s - 1) ^ 2) (by omega)
    _ = (s - 1) ^ 3 := by ring

private theorem suk_scale_lt_carryWidth
    (n s : Nat) (hs : 5 ≤ s) (hlow : (s - 1) ^ 3 < n) :
    s < sukCarryWidth n s := by
  have hcover := sukCarryWidth_cover n s (by omega)
  have hsq : s ^ 2 < n :=
    (suk_scale_sq_le_pred_cube s hs).trans_lt hlow
  by_contra h
  have hwidth : sukCarryWidth n s ≤ s := by omega
  have hmul := Nat.mul_le_mul_left s hwidth
  rw [pow_two] at hsq
  omega

private theorem sukCarryWidth_pred_mul_lt
    (n s : Nat) (hs : 0 < s) (hwidth : 0 < sukCarryWidth n s) :
    (sukCarryWidth n s - 1) * s < n := by
  by_contra h
  have hn : n ≤ (sukCarryWidth n s - 1) * s := by omega
  have hceil : sukCarryWidth n s ≤ sukCarryWidth n s - 1 := by
    change n ⌈/⌉ s ≤ n ⌈/⌉ s - 1
    apply (ceilDiv_le_iff_le_mul hs).2
    simpa [sukCarryWidth, Nat.mul_comm] using hn
  omega

private theorem suk_finalDeficit
    (n s : Nat) (hs : 5 ≤ s) (hlow : (s - 1) ^ 3 < n) :
    2 ≤ n - ((s - 1) * sukCarryWidth n s) := by
  have hscale := suk_scale_lt_carryWidth n s hs hlow
  have hpred := sukCarryWidth_pred_mul_lt n s (by omega) (by omega)
  apply Nat.le_sub_of_add_le
  have hsPred : s - 1 + 1 = s := Nat.sub_add_cancel (by omega)
  have hwidthPred : sukCarryWidth n s - 1 + 1 = sukCarryWidth n s :=
    Nat.sub_add_cancel (by omega)
  have hcompare :
      2 + (s - 1) * sukCarryWidth n s ≤
        (sukCarryWidth n s - 1) * s + 1 := by
    nlinarith
  have hpred' : (sukCarryWidth n s - 1) * s + 1 ≤ n := by omega
  exact hcompare.trans hpred'

/-- The frozen cubic-scale hypotheses produce every natural-number parameter
inequality required by the global finite Suk consumer. -/
theorem sukPositiveFractionParameters_valid
    (n s : Nat)
    (hs : 5 ≤ s)
    (hlow : (s - 1) ^ 3 < n)
    (_hhigh : n ≤ s ^ 3) :
    SukPositiveFractionParameters n s := by
  have hseparatedCover := sukSeparatedCount_cover s
  have hseparated : 3 ≤ sukSeparatedCount s := by omega
  have hfactor : 5 ≤ 2 * sukSeparatedCount s - 1 := by omega
  have hpoolLength : 13 ≤ sukPoolLength s := by
    have hbase : 13 ≤ 5 * 5 := by norm_num
    have hmul : 5 * 5 ≤ sukPoolLength s := by
      simpa [sukPoolLength] using Nat.mul_le_mul hfactor hs
    exact hbase.trans hmul
  have hcarryCover := sukCarryWidth_cover n s (by omega)
  have hscaleCarry := suk_scale_lt_carryWidth n s hs hlow
  have hcarry : 2 ≤ sukCarryWidth n s := by omega
  have hcap : 2 ≤ sukLocalCapSize n s := by
    have hfour := Nat.mul_le_mul_left 2 hcarry
    have hfour' : 4 ≤ sukLocalCapSize n s := by
      simpa [sukLocalCapSize] using hfour
    exact (by omega : 2 ≤ 4).trans hfour'
  have htotal : n ≤ sukSeparatedCount s * sukLocalCapSize n s := by
    calc
      n ≤ s * sukCarryWidth n s := hcarryCover
      _ ≤ (2 * sukSeparatedCount s) * sukCarryWidth n s :=
        Nat.mul_le_mul_right (sukCarryWidth n s) hseparatedCover
      _ = sukSeparatedCount s * sukLocalCapSize n s := by
        simp [sukLocalCapSize, Nat.mul_comm, Nat.mul_left_comm]
  refine {
    poolLengthLower := hpoolLength
    chainSizePositive := by simp [sukChainThreshold]
    antichainSizePositive := by simp [sukAntichainThreshold]
    separatedCountPositive := by omega
    scaleLower := by omega
    poolLengthCovers := by rfl
    carryWidthLower := hcarry
    finalDeficit := suk_finalDeficit n s hs hlow
    finalSize := hcarryCover
    chainCard := ?_
    localCapSizeLower := hcap
    antichainThreshold := by simp [sukAntichainThreshold]
    antichainTotal := htotal
    fineThreshold := by
      exact le_max_left _ _
    coarseThreshold := by
      exact le_max_right _ _
  }
  intro u _hu
  have hchoose := Nat.choose_le_two_pow
    (n + sukCarryWidth n s - 4)
    ((u + 1) * sukCarryWidth n s - 2)
  change Nat.choose (n + sukCarryWidth n s - 4)
      ((u + 1) * sukCarryWidth n s - 2) <
    2 ^ (n + sukCarryWidth n s - 4) + 1
  omega

end

end ErdosSzekeres

end
