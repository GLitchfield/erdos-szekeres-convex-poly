module

public import ErdosSzekeres.DecompositionPrimeMutationLocality

@[expose] public section

/-!
# Strict prime-core-family descent

This file isolates a stronger but simpler Layer-F producer interface.  If a
short target-free realizable mutation macro strictly removes prime cores and
creates none, then the existing stratified rank decreases.  The remaining
geometric obligation is stated without mentioning that rank or the desired
exact upper theorem.
-/

namespace ErdosSzekeres

/-- Above the exact threshold, every target-free realizable indecomposable
coloring has an at-most-three-mutation endpoint whose complete prime-core
family is a strict subset of the source family. -/
def ThreeStepPrimeCoreFamilyShrinksAboveAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}, 2 ^ (k - 2) < n →
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ¬IsDecomposable χ →
    ∃ ψ,
      AtMostThree (TargetFreeRealizableMutationStepAt k) χ ψ ∧
      decompositionPrimeCores ψ ⊂ decompositionPrimeCores χ

/-- Strict inclusion of complete prime-core families decreases the
cardinality-stratified rank. -/
theorem stratifiedPrimeCoreRank_lt_of_primeCoreFamily_ssubset
    {n : ℕ} {χ ψ : TripleColoring n}
    (hproper : decompositionPrimeCores ψ ⊂ decompositionPrimeCores χ) :
    StratifiedPrimeCoreRank ψ < StratifiedPrimeCoreRank χ := by
  classical
  obtain ⟨support, hsupportχ, hsupportψ⟩ :=
    Finset.exists_of_ssubset hproper
  apply Finset.sum_lt_sum_of_subset
      (Finset.ssubset_iff_subset_ne.mp hproper).1
      hsupportχ hsupportψ
  · positivity
  · intro other _ _
    exact Nat.zero_le _

/-- The strict-family producer discharges the existing concrete
three-step-rank interface. -/
theorem threeStepMutationRankDescendsAbove_of_primeCoreFamilyShrinks
    {k : ℕ} (hshrink : ThreeStepPrimeCoreFamilyShrinksAboveAt k) :
    ThreeStepMutationRankDescendsAboveAt k
      (fun _ χ ↦ StratifiedPrimeCoreRank χ) := by
  intro n χ hcard hrealizable htarget hindecomposable
  obtain ⟨ψ, hpath, hproper⟩ :=
    hshrink hcard hrealizable htarget hindecomposable
  exact ⟨ψ, hpath,
    stratifiedPrimeCoreRank_lt_of_primeCoreFamily_ssubset hproper⟩

/-- Strict prime-core-family deletion gives threshold-scoped target-free
normalization by well-founded descent. -/
theorem targetFreeMutationNormalizesAbove_of_primeCoreFamilyShrinks
    {k : ℕ} (hshrink : ThreeStepPrimeCoreFamilyShrinksAboveAt k) :
    TargetFreeMutationNormalizesAboveAt k :=
  targetFreeMutationNormalizesAbove_of_threeStepRankDescent
    (threeStepMutationRankDescendsAbove_of_primeCoreFamilyShrinks hshrink)

/-- The strict-family Layer-F producer promotes the decomposable upper theorem
to the unrestricted sweep-realizable theorem. -/
theorem sweepExactUpperAt_of_primeCoreFamilyShrinks
    {k : ℕ}
    (hdecomposable : DecomposableExactUpperAt k)
    (hshrink : ThreeStepPrimeCoreFamilyShrinksAboveAt k) :
    SweepExactUpperAt k :=
  sweepExactUpperAt_of_mutationNormalizationAbove hdecomposable
    (targetFreeMutationNormalizesAbove_of_primeCoreFamilyShrinks hshrink)

end ErdosSzekeres

end
