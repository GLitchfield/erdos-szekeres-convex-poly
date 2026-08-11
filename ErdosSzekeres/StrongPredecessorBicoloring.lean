module

public import ErdosSzekeres.DecompositionPrimeNormalization
public import ErdosSzekeres.StructuralChargingTransport

@[expose] public section

/-!
# A predecessor-bicoloring route to the exact doubling recurrence

Instead of normalizing a target-free coloring to a decomposition tree, one may
try to partition its vertices into two classes that both avoid the preceding
strong-polygon size. If such a bicoloring exists uniformly, the exact power of
two follows immediately by induction. This file proves the base case and the
generic recurrence consumer; constructing the bicoloring remains a separate
mathematical obligation.
-/

namespace ErdosSzekeres

/-- Every sweep-realizable coloring avoiding a strong `k`-polygon admits a
partition into two classes, each avoiding a strong `(k-1)`-polygon. -/
def StrongPredecessorBicoloringAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ red blue : Finset (Fin n),
      Disjoint red blue ∧
      red ∪ blue = Finset.univ ∧
      ¬ContainsStrongPolygonSet χ red (k - 1) ∧
      ¬ContainsStrongPolygonSet χ blue (k - 1)

/-- A fractional relaxation of predecessor bicoloring. Positive-weight
subsets avoid the predecessor target, every vertex receives total weight at
least one, and the total rational weight is at most two. -/
def FractionalPredecessorCoverAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ w : Finset (Fin n) → ℚ,
      (∀ support, 0 ≤ w support) ∧
      (∀ support, w support ≠ 0 →
        ¬ContainsStrongPolygonSet χ support (k - 1)) ∧
      (∀ vertex, 1 ≤ ∑ support : Finset (Fin n),
        if vertex ∈ support then w support else 0) ∧
      (∑ support : Finset (Fin n), w support) ≤ 2

/-- Three vertices always form a strong polygon, so the exact sweep upper
bound starts at `k = 3`. -/
theorem sweepExactUpperAt_three : SweepExactUpperAt 3 := by
  intro n χ _ hcard
  have hn : 3 ≤ n := by norm_num at hcard ⊢; omega
  let f : Fin 3 ↪o Fin n := Fin.castLEOrderEmb hn
  have hstrong : IsStrongPolygonOn χ f := by
    intro i j k l hij hjk hkl
    omega
  refine ⟨Finset.univ.image f, Finset.subset_univ _, ?_,
    FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

/-- A predecessor bicoloring converts the exact upper bound at `k-1` into the
exact upper bound at `k`. Each color class has at most `2^(k-3)` vertices, so
their disjoint union has at most `2^(k-2)` vertices. -/
theorem sweepExactUpperAt_of_predecessorBicoloring
    {k : ℕ} (hk : 4 ≤ k)
    (hprev : SweepExactUpperAt (k - 1))
    (hbicolor : StrongPredecessorBicoloringAt k) :
    SweepExactUpperAt k := by
  intro n χ hreal hcard
  by_contra hno
  obtain ⟨red, blue, hdisjoint, hunion, hred, hblue⟩ :=
    hbicolor hreal hno
  have hredCard : red.card ≤ 2 ^ (k - 3) := by
    by_contra hlarge
    have hstrict : 2 ^ ((k - 1) - 2) < red.card := by
      have hsub : (k - 1) - 2 = k - 3 := by omega
      rw [hsub]
      omega
    let e : Fin red.card ↪o Fin n := red.orderEmbOfFin rfl
    have hstrong := hprev (hreal.restrict e) hstrict
    have hmapped := containsStrongPolygonSet_map_restrict e hstrong
    rw [Finset.image_orderEmbOfFin_univ] at hmapped
    exact hred hmapped
  have hblueCard : blue.card ≤ 2 ^ (k - 3) := by
    by_contra hlarge
    have hstrict : 2 ^ ((k - 1) - 2) < blue.card := by
      have hsub : (k - 1) - 2 = k - 3 := by omega
      rw [hsub]
      omega
    let e : Fin blue.card ↪o Fin n := blue.orderEmbOfFin rfl
    have hstrong := hprev (hreal.restrict e) hstrict
    have hmapped := containsStrongPolygonSet_map_restrict e hstrong
    rw [Finset.image_orderEmbOfFin_univ] at hmapped
    exact hblue hmapped
  have hn : n = red.card + blue.card := by
    have hunionCard := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisjoint] at hunionCard
    simpa using hunionCard.symm
  have hkpow : k - 2 = (k - 3) + 1 := by omega
  rw [hkpow, pow_succ] at hcard
  omega

/-- A fractional predecessor cover gives the same exact doubling recurrence
as an integral bicoloring. The proof is finite rational double counting: each
positive-weight predecessor-free support has bounded cardinality, while the
cover supplies total vertex incidence at least the ambient cardinality. -/
theorem sweepExactUpperAt_of_fractionalPredecessorCover
    {k : ℕ} (hk : 4 ≤ k)
    (hprev : SweepExactUpperAt (k - 1))
    (hfrac : FractionalPredecessorCoverAt k) :
    SweepExactUpperAt k := by
  intro n χ hreal hcard
  by_contra hno
  obtain ⟨w, hnonneg, hfree, hcover, htotal⟩ := hfrac hreal hno
  have hsupportCard (support : Finset (Fin n)) (hw : w support ≠ 0) :
      support.card ≤ 2 ^ (k - 3) := by
    by_contra hlarge
    have hstrict : 2 ^ ((k - 1) - 2) < support.card := by
      have hsub : (k - 1) - 2 = k - 3 := by omega
      rw [hsub]
      omega
    let e : Fin support.card ↪o Fin n := support.orderEmbOfFin rfl
    have hstrong := hprev (hreal.restrict e) hstrict
    have hmapped := containsStrongPolygonSet_map_restrict e hstrong
    rw [Finset.image_orderEmbOfFin_univ] at hmapped
    exact (hfree support hw) hmapped
  have hdouble :
      (n : ℚ) ≤ ((2 ^ (k - 3) : ℕ) : ℚ) * 2 := by
    calc
      (n : ℚ) = ∑ _vertex : Fin n, (1 : ℚ) := by simp
      _ ≤ ∑ vertex : Fin n, ∑ support : Finset (Fin n),
          if vertex ∈ support then w support else 0 := by
        exact Finset.sum_le_sum fun vertex _ ↦ hcover vertex
      _ = ∑ support : Finset (Fin n),
          (support.card : ℚ) * w support := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro support _
        simp [nsmul_eq_mul]
      _ ≤ ∑ support : Finset (Fin n),
          ((2 ^ (k - 3) : ℕ) : ℚ) * w support := by
        apply Finset.sum_le_sum
        intro support _
        by_cases hw : w support = 0
        · simp [hw]
        · exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hsupportCard support hw) (hnonneg support)
      _ = ((2 ^ (k - 3) : ℕ) : ℚ) *
          ∑ support : Finset (Fin n), w support := by
        rw [Finset.mul_sum]
      _ ≤ ((2 ^ (k - 3) : ℕ) : ℚ) * 2 :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
  have hn : n ≤ 2 ^ (k - 3) * 2 := by
    exact_mod_cast hdouble
  have hkpow : k - 2 = (k - 3) + 1 := by omega
  rw [hkpow, pow_succ] at hcard
  omega

end ErdosSzekeres

end
