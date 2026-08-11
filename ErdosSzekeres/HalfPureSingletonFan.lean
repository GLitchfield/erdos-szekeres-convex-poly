module

public import ErdosSzekeres.InverseSteppingUpKernel

@[expose] public section

/-!
# Thresholded singleton-fan predecessor producer

Above the range already covered by the elementary predecessor bicoloring, a
single exterior pivot and a half-sized pure side of a deep-below split suffice
for the predecessor half-subset recurrence.  This file isolates that exact
structural producer and its certificate-free consumer.
-/

namespace ErdosSzekeres

/-- Above the elementary bicoloring threshold, a target-free realizable
coloring has a half-sized side joined to an exterior singleton by a deep split.
Every predecessor polygon on that side is pure in the direction required by
the corresponding inverse stepping-up kernel. -/
def HalfPureSingletonFanProducerAboveAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    2 * k - 3 < n →
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ side : Finset (Fin n), ∃ pivot : Fin n,
      pivot ∉ side ∧
      n ≤ 2 * side.card ∧
      ((HasDeepBelowSplit χ side {pivot} ∧
          ∀ polygon : Finset (Fin n),
            polygon ⊆ side → polygon.card = k - 1 →
              IsStrongPolygonSet χ polygon → IsCupSet χ polygon) ∨
       (HasDeepBelowSplit χ {pivot} side ∧
          ∀ polygon : Finset (Fin n),
            polygon ⊆ side → polygon.card = k - 1 →
              IsStrongPolygonSet χ polygon → IsCapSet χ polygon))

/-- The thresholded singleton-fan producer implies the generic predecessor
half-subset contract.  At or below `2 * k - 3`, the existing elementary
bicoloring theorem supplies the half-subset; above it, the singleton fan feeds
one of the two inverse stepping-up kernels. -/
theorem predecessorHalfSubsetAt_of_halfPureSingletonFanProducerAbove
    {k : ℕ} (hk : 5 ≤ k)
    (hfan : HalfPureSingletonFanProducerAboveAt k) :
    PredecessorHalfSubsetAt k := by
  intro n χ hrealizable hnoStrong
  by_cases hn : n ≤ 2 * k - 3
  · obtain ⟨red, blue, hdisjoint, hunion, hred, hblue⟩ :=
      exists_strongPredecessorBicoloring_of_card_le_two_mul_sub_three
        hk hn hnoStrong
    have hcard : n = red.card + blue.card := by
      have hunionCard := congrArg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisjoint] at hunionCard
      simpa using hunionCard.symm
    by_cases hle : blue.card ≤ red.card
    · exact ⟨red, hred, by omega⟩
    · exact ⟨blue, hblue, by omega⟩
  · have habove : 2 * k - 3 < n := by omega
    obtain ⟨side, pivot, _hpivot, hhalf, hbranch⟩ :=
      hfan habove hrealizable hnoStrong
    rcases hbranch with hlower | hupper
    · exact ⟨side,
        hlower.1.predecessorFree_lower_of_cupPure
          (by omega) (by simp) hnoStrong hlower.2,
        hhalf⟩
    · exact ⟨side,
        hupper.1.predecessorFree_upper_of_capPure
          (by omega) (by simp) hnoStrong hupper.2,
        hhalf⟩

end ErdosSzekeres

end
