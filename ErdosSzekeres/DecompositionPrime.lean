module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Decomposition-prime subsets

This file isolates the finite minimal obstruction to recursive deep-below
decomposition.  It is infrastructure for the unrestricted Layer-F bridge;
it does not claim that a small prime core alone proves the exact bound.
-/

namespace ErdosSzekeres

/-- A genuine deep-below split whose two sides are nonempty and cover the
given support. -/
def HasProperDeepBelowSplitOn {n : ℕ} (χ : TripleColoring n)
    (support : Finset (Fin n)) : Prop :=
  ∃ lower upper : Finset (Fin n),
    lower.Nonempty ∧ upper.Nonempty ∧ lower ∪ upper = support ∧
      HasDeepBelowSplit χ lower upper

/-- A support of cardinality at least two with no proper deep-below split. -/
def IsDecompositionPrimeOn {n : ℕ} (χ : TripleColoring n)
    (support : Finset (Fin n)) : Prop :=
  2 ≤ support.card ∧ ¬HasProperDeepBelowSplitOn χ support

/-- An indecomposable support all of whose nonempty proper subsets are
decomposable. -/
def IsDeletionMinimalIndecomposableOn {n : ℕ} (χ : TripleColoring n)
    (support : Finset (Fin n)) : Prop :=
  support.Nonempty ∧ ¬IsDecomposableOn χ support ∧
    ∀ subset, subset ⊂ support → subset.Nonempty →
      IsDecomposableOn χ subset

/-- Every nonempty indecomposable support contains a deletion-minimal
indecomposable subset, and every such minimum is decomposition-prime. -/
theorem exists_deletionMinimal_indec_prime
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (hsupport : support.Nonempty)
    (hindecomposable : ¬IsDecomposableOn χ support) :
    ∃ prime,
      prime ⊆ support ∧
      IsDeletionMinimalIndecomposableOn χ prime ∧
      IsDecompositionPrimeOn χ prime := by
  classical
  induction hcard : support.card using Nat.strong_induction_on generalizing support with
  | h card ih =>
      by_cases hsmaller : ∃ subset, subset ⊂ support ∧ subset.Nonempty ∧
          ¬IsDecomposableOn χ subset
      · obtain ⟨subset, hproper, hsubsetNonempty, hsubsetIndec⟩ := hsmaller
        obtain ⟨prime, hprimeSub, hminimal, hprime⟩ :=
          ih subset.card (by
            have := Finset.card_lt_card hproper
            omega) (support := subset) hsubsetNonempty hsubsetIndec rfl
        exact ⟨prime,
          hprimeSub.trans (Finset.ssubset_iff_subset_ne.mp hproper).1,
          hminimal, hprime⟩
      · have hminimal : IsDeletionMinimalIndecomposableOn χ support := by
          refine ⟨hsupport, hindecomposable, ?_⟩
          intro subset hproper hsubsetNonempty
          by_contra hsubsetIndec
          exact hsmaller ⟨subset, hproper, hsubsetNonempty, hsubsetIndec⟩
        have hcardTwo : 2 ≤ support.card := by
          by_contra hsmall
          have hcardOne : support.card = 1 := by
            have hpositive := Finset.card_pos.mpr hsupport
            omega
          obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcardOne
          exact hindecomposable (IsDecomposableOn.singleton x)
        have hprime : IsDecompositionPrimeOn χ support := by
          refine ⟨hcardTwo, ?_⟩
          rintro ⟨lower, upper, hlower, hupper, hunion, hdeep⟩
          have hlowerSub : lower ⊆ support := by
            rw [← hunion]
            exact Finset.subset_union_left
          have hupperSub : upper ⊆ support := by
            rw [← hunion]
            exact Finset.subset_union_right
          have hlowerNe : lower ≠ support := by
            intro heq
            obtain ⟨x, hxUpper⟩ := hupper
            have hxLower : x ∈ lower := by
              simpa [heq] using hupperSub hxUpper
            exact (Finset.disjoint_left.mp hdeep.disjoint) hxLower hxUpper
          have hupperNe : upper ≠ support := by
            intro heq
            obtain ⟨x, hxLower⟩ := hlower
            have hxUpper : x ∈ upper := by
              simpa [heq] using hlowerSub hxLower
            exact (Finset.disjoint_left.mp hdeep.disjoint) hxLower hxUpper
          have hlowerProper : lower ⊂ support :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hlowerSub, hlowerNe⟩
          have hupperProper : upper ⊂ support :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hupperSub, hupperNe⟩
          have hlowerDecomp := hminimal.2.2 lower hlowerProper hlower
          have hupperDecomp := hminimal.2.2 upper hupperProper hupper
          apply hindecomposable
          rw [← hunion]
          exact IsDecomposableOn.split hlowerDecomp hupperDecomp hdeep
        exact ⟨support, Finset.Subset.rfl, hminimal, hprime⟩

end ErdosSzekeres

end
