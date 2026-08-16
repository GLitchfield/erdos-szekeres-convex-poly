module

public import ErdosSzekeres.PorValtrCyclicSupportCarrierBridge
public import ErdosSzekeres.PorValtrPointSetProducer
public import ErdosSzekeres.SukPositiveFractionParameters

@[expose] public section

/-!
# Suk's exact positive-fraction threshold

This module composes the original-carrier Pór--Valtr point-set source with the
finite global Suk consumer at the rounding-safe natural-number parameters.
-/

namespace ErdosSzekeres

noncomputable section

private theorem porValtrOpenPoolLowerBound_cover
    {N r : ℕ} (hlarge : porValtrSupportDenominator r < N) :
    N ≤ porValtrSupportDenominator r *
      (porValtrOpenPoolLowerBound N r + 1) := by
  have hdenominatorPositive : 0 < porValtrSupportDenominator r := by
    simp [porValtrSupportDenominator]
  have hceilCover :
      N ≤ porValtrSupportDenominator r *
        (N ⌈/⌉ porValtrSupportDenominator r) :=
    (ceilDiv_le_iff_le_mul hdenominatorPositive).1 le_rfl
  have hceilPositive :
      1 ≤ N ⌈/⌉ porValtrSupportDenominator r := by
    by_contra h
    have hceilZero : N ⌈/⌉ porValtrSupportDenominator r = 0 := by
      omega
    rw [hceilZero, Nat.mul_zero] at hceilCover
    omega
  have hlowerSucc :
      porValtrOpenPoolLowerBound N r + 1 =
        N ⌈/⌉ porValtrSupportDenominator r := by
    simpa only [porValtrOpenPoolLowerBound, Nat.ceilDiv_eq_add_pred_div] using
      (Nat.sub_add_cancel hceilPositive)
  rw [hlowerSucc]
  exact hceilCover

/-- The exact frozen threshold forces an `n`-point convex subset in every
sufficiently large original planar point set. -/
theorem sukPositiveFraction_forces_threshold
    (n s : Nat)
    (hs : 5 ≤ s)
    (hlow : (s - 1) ^ 3 < n)
    (hhigh : n ≤ s ^ 3) :
    ForcesConvexPolygon n (sukPositiveFractionThreshold n s) := by
  intro P hcard hgeneral
  let params := sukPositiveFractionParameters_valid n s hs hlow hhigh
  have hsourceLarge :
      porValtrSupportDenominator (sukPoolLength s + 3) < P.card := by
    change porValtrFineDenominator (sukPoolLength s) < P.card
    have hpositive : 0 < porValtrFineDenominator (sukPoolLength s) := by
      simp [porValtrFineDenominator]
    have hthreshold := params.fineThreshold.trans hcard
    omega
  obtain ⟨data, hdataCarrier⟩ :=
    exists_porValtrCyclicSupportData P (sukPoolLength s + 3)
      (by omega) hsourceLarge hgeneral
  obtain ⟨anchors, pools, hraw, hsourceCard, hpoolsCarrier⟩ :=
    data.toSukConsecutiveRawPoolsWithCarrier (by
      have := params.poolLengthLower
      omega)
  simp only [Nat.add_sub_cancel] at hraw hsourceCard hpoolsCarrier
  have hsourceCover :
      P.card ≤ porValtrFineDenominator (sukPoolLength s) *
        (porValtrOpenPoolLowerBound P.card (sukPoolLength s + 3) + 1) := by
    rw [← show porValtrSupportDenominator (sukPoolLength s + 3) =
      porValtrFineDenominator (sukPoolLength s) by rfl]
    exact porValtrOpenPoolLowerBound_cover hsourceLarge
  have hdensity :
      P.card ≤ sukCoarseDenominator (sukPoolLength s) *
        porValtrOpenPoolLowerBound P.card (sukPoolLength s + 3) :=
    porValtrMinusOne_to_sukCoarseDensity
      params.poolLengthLower (params.fineThreshold.trans hcard) hsourceCover
  have hpoolCard : ∀ i, i < sukPoolLength s →
      (sukChainThreshold n s - 1) *
          (sukAntichainThreshold n s - 1) <
        (pools i).card := by
    intro i hi
    have hscaled :
        sukCoarseDenominator (sukPoolLength s) *
            ((sukChainThreshold n s - 1) *
              (sukAntichainThreshold n s - 1) + 1) ≤
          sukCoarseDenominator (sukPoolLength s) *
            porValtrOpenPoolLowerBound P.card (sukPoolLength s + 3) :=
      (params.coarseThreshold.trans hcard).trans hdensity
    have hcoarsePositive : 0 < sukCoarseDenominator (sukPoolLength s) := by
      simp [sukCoarseDenominator]
    have hlower :
        (sukChainThreshold n s - 1) *
            (sukAntichainThreshold n s - 1) + 1 ≤
          porValtrOpenPoolLowerBound P.card (sukPoolLength s + 3) :=
      le_of_mul_le_mul_left hscaled hcoarsePositive
    have hsource := hsourceCard i hi
    omega
  have hconvex :
      ContainsConvexSubset (SukConsecutivePoolCarrier (sukPoolLength s) pools) n :=
    hraw.containsConvexSubset_of_globalParameters
      params.chainSizePositive params.antichainSizePositive
      params.separatedCountPositive params.scaleLower params.poolLengthCovers
      hpoolCard params.carryWidthLower params.finalDeficit params.finalSize
      params.chainCard params.localCapSizeLower params.antichainThreshold
      params.antichainTotal
  have hpoolsSubset : ∀ i, i < sukPoolLength s → pools i ⊆ P := by
    intro i hi
    rw [← hdataCarrier]
    exact hpoolsCarrier i hi
  have hcarrierSubset :
      SukConsecutivePoolCarrier (sukPoolLength s) pools ⊆ P := by
    intro p hp
    rw [SukConsecutivePoolCarrier] at hp
    rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
    exact hpoolsSubset i (Finset.mem_range.mp hi) hpi
  rcases hconvex with ⟨selected, hselected, hselectedCard, hselectedConvex⟩
  exact ⟨selected, hselected.trans hcarrierSubset, hselectedCard, hselectedConvex⟩

end

end ErdosSzekeres

end
