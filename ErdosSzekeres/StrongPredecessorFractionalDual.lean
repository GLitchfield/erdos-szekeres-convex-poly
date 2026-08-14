module

public import ErdosSzekeres.StrongPredecessorBicoloring

@[expose] public section

/-!
# The half-mass dual of fractional predecessor covering

This file isolates the elementary weighted statement dual to the fractional
predecessor-cover route.  Only the easy finite rational implications are proved
here; no linear-programming duality theorem is assumed.
-/

namespace ErdosSzekeres

/-- Every normalized nonnegative vertex weighting places at least half its mass
on some predecessor-free support. -/
def PredecessorHalfMassAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∀ μ : Fin n → ℚ,
      (∀ vertex, 0 ≤ μ vertex) →
      (∑ vertex, μ vertex) = 1 →
      ∃ support : Finset (Fin n),
        ¬ContainsStrongPolygonSet χ support (k - 1) ∧
        1 / 2 ≤ ∑ vertex ∈ support, μ vertex

/-- A fractional predecessor cover implies the half-mass property by finite
rational double counting. -/
theorem predecessorHalfMassAt_of_fractionalCover
    {k : ℕ} (hfrac : FractionalPredecessorCoverAt k) :
    PredecessorHalfMassAt k := by
  classical
  intro n χ hreal hno μ hμnonneg hμsum
  obtain ⟨w, hwnonneg, hwfree, hwcover, hwtotal⟩ := hfrac hreal hno
  let mass : Finset (Fin n) → ℚ := fun support ↦ ∑ vertex ∈ support, μ vertex
  by_contra hnone
  push Not at hnone
  have hnpos : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp at hμsum
  have hwpositive : ∃ support : Finset (Fin n), 0 < w support := by
    by_contra hnot
    push Not at hnot
    have hwzero (support : Finset (Fin n)) : w support = 0 :=
      le_antisymm (hnot support) (hwnonneg support)
    have hcover := hwcover (⟨0, hnpos⟩ : Fin n)
    simp [hwzero] at hcover
    linarith
  obtain ⟨strictSupport, hstrictSupport⟩ := hwpositive
  have hmassNonneg (support : Finset (Fin n)) : 0 ≤ mass support := by
    exact Finset.sum_nonneg fun _ _ ↦ hμnonneg _
  have hmassSmall (support : Finset (Fin n)) (hw : w support ≠ 0) :
      mass support < 1 / 2 := by
    exact hnone support (hwfree support hw)
  have hweightedIncidence :
      (∑ vertex : Fin n, μ vertex *
          ∑ support : Finset (Fin n), if vertex ∈ support then w support else 0) =
        ∑ support : Finset (Fin n), w support * mass support := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro support _
    simp [mass, Finset.mul_sum, mul_comm]
  have hincidenceLower :
      (1 : ℚ) ≤ ∑ support : Finset (Fin n), w support * mass support := by
    rw [← hweightedIncidence, ← hμsum]
    apply Finset.sum_le_sum
    intro vertex _
    calc
      μ vertex = μ vertex * 1 := by ring
      _ ≤ μ vertex *
          ∑ support : Finset (Fin n), if vertex ∈ support then w support else 0 :=
        mul_le_mul_of_nonneg_left (hwcover vertex) (hμnonneg vertex)
  have htermLe (support : Finset (Fin n)) :
      w support * mass support ≤ w support * (1 / 2) := by
    by_cases hw : w support = 0
    · simp [hw]
    · exact mul_le_mul_of_nonneg_left (hmassSmall support hw).le (hwnonneg support)
  have htermLt :
      w strictSupport * mass strictSupport < w strictSupport * (1 / 2) := by
    exact mul_lt_mul_of_pos_left
      (hmassSmall strictSupport hstrictSupport.ne') hstrictSupport
  have hweightedStrict :
      (∑ support : Finset (Fin n), w support * mass support) <
        ∑ support : Finset (Fin n), w support * (1 / 2) := by
    exact Finset.sum_lt_sum (fun support _ ↦ htermLe support)
      ⟨strictSupport, Finset.mem_univ _, htermLt⟩
  have htotalUpper :
      (∑ support : Finset (Fin n), w support * (1 / 2)) ≤ 1 := by
    rw [← Finset.sum_mul]
    nlinarith
  linarith

/-- The half-mass property implies the unweighted predecessor-half-subset
contract by applying it to uniform vertex mass. -/
theorem predecessorHalfSubsetAt_of_halfMass
    {k : ℕ} (hk : 2 ≤ k) (hhalfMass : PredecessorHalfMassAt k) :
    PredecessorHalfSubsetAt k := by
  intro n χ hreal hno
  by_cases hn : n = 0
  · subst n
    refine ⟨∅, ?_, by simp⟩
    rintro ⟨polygon, hpolygonSub, hpolygonCard, _⟩
    have hpolygon : polygon = ∅ := Finset.subset_empty.mp hpolygonSub
    subst polygon
    simp at hpolygonCard
    omega
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnposQ : (0 : ℚ) < n := by exact_mod_cast hnpos
    let μ : Fin n → ℚ := fun _ ↦ 1 / n
    have hμnonneg (vertex : Fin n) : 0 ≤ μ vertex := by
      dsimp [μ]
      positivity
    have hμsum : (∑ vertex, μ vertex) = 1 := by
      simp [μ, nsmul_eq_mul, hn]
    obtain ⟨support, hfree, hmass⟩ :=
      hhalfMass hreal hno μ hμnonneg hμsum
    refine ⟨support, hfree, ?_⟩
    have hmass' :
        (1 : ℚ) / 2 ≤ (support.card : ℚ) / n := by
      simpa [μ, nsmul_eq_mul] using hmass
    have hscaled : (n : ℚ) / 2 ≤ support.card := by
      have := (le_div_iff₀ hnposQ).mp hmass'
      simpa [div_eq_mul_inv, mul_comm] using this
    exact_mod_cast (show (n : ℚ) ≤ 2 * support.card by linarith)

/-- The half-mass property gives the exact sweep recurrence through the existing
predecessor-half-subset consumer. -/
theorem sweepExactUpperAt_of_predecessorHalfMass
    {k : ℕ} (hk : 4 ≤ k)
    (hprev : SweepExactUpperAt (k - 1))
    (hhalfMass : PredecessorHalfMassAt k) :
    SweepExactUpperAt k := by
  exact sweepExactUpperAt_of_predecessorHalfSubset hk hprev
    (predecessorHalfSubsetAt_of_halfMass (by omega) hhalfMass)

end ErdosSzekeres
