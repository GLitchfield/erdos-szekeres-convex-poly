module

public import ErdosSzekeres.DecompositionPrimeNormalization

@[expose] public section

/-!
# A noncircular mutation rank from decomposition-prime cores

This file defines the number of decomposition-prime restrictions of a triple
coloring. On a nonempty ground set the count vanishes exactly for recursively
decomposable colorings. It is therefore a concrete candidate rank for the
three-step mutation-descent interface.
-/

namespace ErdosSzekeres

/-- All restrictions of a coloring that are prime for recursive deep-below
decomposition. -/
noncomputable def decompositionPrimeCores
    {n : ℕ} (χ : TripleColoring n) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.powerset.filter fun support ↦
    IsDecompositionPrimeOn χ support

theorem mem_decompositionPrimeCores_iff
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)} :
    support ∈ decompositionPrimeCores χ ↔
      IsDecompositionPrimeOn χ support := by
  classical
  simp [decompositionPrimeCores]

/-- The number of decomposition-prime restrictions of a coloring. -/
noncomputable def PrimeCoreCount
    {n : ℕ} (χ : TripleColoring n) : ℕ :=
  (decompositionPrimeCores χ).card

/-- On a nonempty ground set, a coloring has no prime restriction exactly
when the whole coloring is recursively decomposable. -/
theorem primeCoreCount_eq_zero_iff
    {n : ℕ} {χ : TripleColoring n} (hn : 0 < n) :
    PrimeCoreCount χ = 0 ↔ IsDecomposable χ := by
  constructor
  · intro hzero
    by_contra hindecomposable
    have hunivNonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
      exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    obtain ⟨prime, _, _, hprime⟩ :=
      exists_deletionMinimal_indec_prime hunivNonempty hindecomposable
    have hmem : prime ∈ decompositionPrimeCores χ :=
      mem_decompositionPrimeCores_iff.mpr hprime
    have hpositive : 0 < PrimeCoreCount χ := by
      exact Finset.card_pos.mpr ⟨prime, hmem⟩
    omega
  · intro hdecomposable
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨prime, hmem⟩
    have hprime : IsDecompositionPrimeOn χ prime :=
      mem_decompositionPrimeCores_iff.mp hmem
    have hprimeNonempty : prime.Nonempty :=
      Finset.card_pos.mp (lt_of_lt_of_le (by omega) hprime.1)
    have hprimeDecomposable := hdecomposable.subset
      (Finset.subset_univ prime) hprimeNonempty
    obtain ⟨lower, upper, hlower, hupper, _, _, hdeep, hunion⟩ :=
      hprimeDecomposable.exists_split hprime.1
    exact hprime.2 ⟨lower, upper, hlower, hupper, hunion.symm, hdeep⟩

end ErdosSzekeres

end
