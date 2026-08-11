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

/-- A weaker predecessor contract sufficient for exact doubling: every
strong-`k`-free realizable coloring has one strong-`(k-1)`-free support
containing at least half of its vertices. -/
def PredecessorHalfSubsetAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ support : Finset (Fin n),
      ¬ContainsStrongPolygonSet χ support (k - 1) ∧
      n ≤ 2 * support.card

/-- If every predecessor-sized subset of a set with at least five vertices is
strong, then the whole set is strong.  Every ordered quadruple survives after
erasing some fifth vertex, so the four-index law is inherited from a
predecessor subset. -/
theorem isStrongPolygonSet_of_all_pred_subsets
    {n k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hk : 5 ≤ k) (hcard : s.card = k)
    (hall : ∀ t : Finset (Fin n), t ⊆ s → t.card = k - 1 →
      IsStrongPolygonSet χ t) :
    IsStrongPolygonSet χ s := by
  intro i j m l hij hjm hml hi hj hm hl
  let quad : Finset (Fin n) := {i, j, m, l}
  have hquadCard : quad.card = 4 := by
    simp [quad, ne_of_lt hij, ne_of_lt (hij.trans hjm),
      ne_of_lt (hij.trans (hjm.trans hml)), ne_of_lt hjm,
      ne_of_lt (hjm.trans hml), ne_of_lt hml]
  have hnotSubset : ¬s ⊆ quad := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hcard, hquadCard] at hle
    omega
  obtain ⟨x, hxs, hxquad⟩ := Finset.not_subset.mp hnotSubset
  have hxi : x ≠ i := by
    intro hxi
    subst x
    exact hxquad (by simp [quad])
  have hxj : x ≠ j := by
    intro hxj
    subst x
    exact hxquad (by simp [quad])
  have hxm : x ≠ m := by
    intro hxm
    subst x
    exact hxquad (by simp [quad])
  have hxl : x ≠ l := by
    intro hxl
    subst x
    exact hxquad (by simp [quad])
  have htCard : (s.erase x).card = k - 1 := by
    rw [Finset.card_erase_of_mem hxs, hcard]
  exact hall (s.erase x) (Finset.erase_subset _ _) htCard hij hjm hml
    (Finset.mem_erase.mpr ⟨hxi.symm, hi⟩)
    (Finset.mem_erase.mpr ⟨hxj.symm, hj⟩)
    (Finset.mem_erase.mpr ⟨hxm.symm, hm⟩)
    (Finset.mem_erase.mpr ⟨hxl.symm, hl⟩)

/-- On at most `2 * k - 3` vertices, strong-`k` avoidance already forces a
predecessor bicoloring.  Below the boundary the two classes can both be made
too small to contain `k-1` vertices.  At equality, failure of every
predecessor set would make every `k`-set strong by the local four-index law. -/
theorem exists_strongPredecessorBicoloring_of_card_le_two_mul_sub_three
    {k : ℕ} (hk : 5 ≤ k) :
    ∀ {n : ℕ} {χ : TripleColoring n},
      n ≤ 2 * k - 3 →
      ¬ContainsStrongPolygonSet χ Finset.univ k →
      ∃ red blue : Finset (Fin n),
        Disjoint red blue ∧
        red ∪ blue = Finset.univ ∧
        ¬ContainsStrongPolygonSet χ red (k - 1) ∧
        ¬ContainsStrongPolygonSet χ blue (k - 1) := by
  intro n χ hn hnoStrong
  have small_is_free (support : Finset (Fin n))
      (hsmall : support.card < k - 1) :
      ¬ContainsStrongPolygonSet χ support (k - 1) := by
    rintro ⟨polygon, hsub, hcard, _⟩
    have hle := Finset.card_le_card hsub
    omega
  by_cases hlow : n ≤ 2 * (k - 2)
  · by_cases hnSmall : n ≤ k - 2
    · refine ⟨Finset.univ, ∅, Finset.disjoint_empty_right _,
        by simp, ?_, small_is_free ∅ (by simp; omega)⟩
      apply small_is_free
      simp
      omega
    · have hredExists : ∃ red : Finset (Fin n),
          red ⊆ Finset.univ ∧ red.card = k - 2 := by
        apply Finset.exists_subset_card_eq
        simp
        omega
      obtain ⟨red, hredSub, hredCard⟩ := hredExists
      let blue := Finset.univ \ red
      have hblueCard : blue.card ≤ k - 2 := by
        dsimp [blue]
        rw [Finset.card_sdiff_of_subset hredSub]
        simp
        omega
      refine ⟨red, blue, Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hredSub, ?_, ?_⟩
      · apply small_is_free
        rw [hredCard]
        omega
      · apply small_is_free
        omega
  · have hnEq : n = 2 * k - 3 := by omega
    have hfreePred : ∃ red : Finset (Fin n),
        red ⊆ Finset.univ ∧ red.card = k - 1 ∧
        ¬IsStrongPolygonSet χ red := by
      by_contra hnone
      push Not at hnone
      have hkLeN : k ≤ n := by omega
      obtain ⟨polygon, hpolygonSub, hpolygonCard⟩ :=
        Finset.exists_subset_card_eq
          (s := (Finset.univ : Finset (Fin n))) (by simpa using hkLeN)
      have hpolygonStrong : IsStrongPolygonSet χ polygon := by
        apply isStrongPolygonSet_of_all_pred_subsets hk hpolygonCard
        intro t htSub htCard
        exact hnone t (htSub.trans hpolygonSub) htCard
      exact hnoStrong ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩
    obtain ⟨red, hredSub, hredCard, hredFree⟩ := hfreePred
    let blue := Finset.univ \ red
    have hblueCard : blue.card = k - 2 := by
      dsimp [blue]
      rw [Finset.card_sdiff_of_subset hredSub]
      simp [hnEq, hredCard]
      omega
    refine ⟨red, blue, Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hredSub, ?_, ?_⟩
    · rintro ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩
      have hpolygonEq : polygon = red :=
        Finset.eq_of_subset_of_card_le hpolygonSub (by omega)
      subst polygon
      exact hredFree hpolygonStrong
    · apply small_is_free
      rw [hblueCard]
      omega

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

/-- One predecessor-free support containing at least half of the vertices
gives the same exact doubling recurrence as a full predecessor bicoloring. -/
theorem sweepExactUpperAt_of_predecessorHalfSubset
    {k : ℕ} (hk : 4 ≤ k)
    (hprev : SweepExactUpperAt (k - 1))
    (hhalf : PredecessorHalfSubsetAt k) :
    SweepExactUpperAt k := by
  intro n χ hreal hcard
  by_contra hno
  obtain ⟨support, hfree, hhalfCard⟩ := hhalf hreal hno
  have hsupportCard : support.card ≤ 2 ^ (k - 3) := by
    by_contra hlarge
    have hstrict : 2 ^ ((k - 1) - 2) < support.card := by
      have hsub : (k - 1) - 2 = k - 3 := by omega
      rw [hsub]
      omega
    let e : Fin support.card ↪o Fin n := support.orderEmbOfFin rfl
    have hstrong := hprev (hreal.restrict e) hstrict
    have hmapped := containsStrongPolygonSet_map_restrict e hstrong
    rw [Finset.image_orderEmbOfFin_univ] at hmapped
    exact hfree hmapped
  have hkpow : k - 2 = (k - 3) + 1 := by omega
  rw [hkpow, pow_succ] at hcard
  omega

/-- Integral predecessor bicoloring implies the weaker half-subset
contract by selecting the larger color class. -/
theorem predecessorHalfSubsetAt_of_bicoloring
    {k : ℕ} (hbicolor : StrongPredecessorBicoloringAt k) :
    PredecessorHalfSubsetAt k := by
  intro n χ hreal hno
  obtain ⟨red, blue, hdisjoint, hunion, hred, hblue⟩ :=
    hbicolor hreal hno
  have hn : n = red.card + blue.card := by
    have hunionCard := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisjoint] at hunionCard
    simpa using hunionCard.symm
  by_cases hle : blue.card ≤ red.card
  · exact ⟨red, hred, by omega⟩
  · exact ⟨blue, hblue, by omega⟩

/-- Integral predecessor bicoloring implies the fractional relaxation by
putting weight one on each color class.  If both classes are empty, their
coincident support simply receives weight two. -/
theorem fractionalPredecessorCoverAt_of_bicoloring
    {k : ℕ} (hbicolor : StrongPredecessorBicoloringAt k) :
    FractionalPredecessorCoverAt k := by
  intro n χ hreal hno
  obtain ⟨red, blue, _hdisjoint, hunion, hred, hblue⟩ :=
    hbicolor hreal hno
  let w : Finset (Fin n) → ℚ := fun support ↦
    (if support = red then 1 else 0) +
      (if support = blue then 1 else 0)
  have hwNonneg (support : Finset (Fin n)) : 0 ≤ w support := by
    dsimp [w]
    positivity
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · exact hwNonneg
  · intro support hpositive
    by_cases hsupportRed : support = red
    · simpa [hsupportRed] using hred
    · by_cases hsupportBlue : support = blue
      · simpa [hsupportBlue] using hblue
      · simp [w, hsupportRed, hsupportBlue] at hpositive
  · intro vertex
    let incidenceWeight : Finset (Fin n) → ℚ := fun support ↦
      if vertex ∈ support then w support else 0
    have hincidenceNonneg (support : Finset (Fin n)) :
        0 ≤ incidenceWeight support := by
      dsimp [incidenceWeight]
      by_cases hmem : vertex ∈ support
      · rw [if_pos hmem]
        exact hwNonneg support
      · rw [if_neg hmem]
    have hvertex : vertex ∈ red ∨ vertex ∈ blue := by
      rw [← Finset.mem_union]
      simp [hunion]
    rcases hvertex with hvertexRed | hvertexBlue
    · have hterm : incidenceWeight red ≤
          ∑ support : Finset (Fin n), incidenceWeight support :=
        Finset.single_le_sum
          (fun support (_ : support ∈ Finset.univ) ↦ hincidenceNonneg support)
          (Finset.mem_univ red)
      calc
        1 ≤ incidenceWeight red := by
          dsimp [incidenceWeight, w]
          rw [if_pos hvertexRed, if_pos rfl]
          by_cases hEq : red = blue <;> simp [hEq]
        _ ≤ _ := hterm
    · have hterm : incidenceWeight blue ≤
          ∑ support : Finset (Fin n), incidenceWeight support :=
        Finset.single_le_sum
          (fun support (_ : support ∈ Finset.univ) ↦ hincidenceNonneg support)
          (Finset.mem_univ blue)
      calc
        1 ≤ incidenceWeight blue := by
          dsimp [incidenceWeight, w]
          rw [if_pos hvertexBlue, if_pos rfl]
          by_cases hEq : blue = red <;> simp [hEq]
        _ ≤ _ := hterm
  · norm_num [w, Finset.sum_add_distrib]

/-- A fractional predecessor cover also contains one positive-weight support
holding at least half of the vertices. This is the unweighted averaging
consequence of the fractional cover inequalities. -/
theorem predecessorHalfSubsetAt_of_fractionalCover
    {k : ℕ} (hk : 2 ≤ k) (hfrac : FractionalPredecessorCoverAt k) :
    PredecessorHalfSubsetAt k := by
  intro n χ hreal hno
  obtain ⟨w, hnonneg, hfree, hcover, htotal⟩ := hfrac hreal hno
  by_cases hn : n = 0
  · subst n
    refine ⟨∅, ?_, by simp⟩
    rintro ⟨polygon, hpolygonSub, hpolygonCard, _⟩
    have hpolygon : polygon = ∅ := Finset.subset_empty.mp hpolygonSub
    subst polygon
    simp at hpolygonCard
    omega
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_contra hnone
    have hsmall (support : Finset (Fin n)) (hw : w support ≠ 0) :
        2 * support.card < n := by
      by_contra hnot
      apply hnone
      exact ⟨support, hfree support hw, by omega⟩
    have hpositive : ∃ support : Finset (Fin n), 0 < w support := by
      by_contra hnonePositive
      have hzero (support : Finset (Fin n)) : w support = 0 := by
        apply le_antisymm
        · exact le_of_not_gt fun hgt ↦ hnonePositive ⟨support, hgt⟩
        · exact hnonneg support
      have hcover0 := hcover (⟨0, hnpos⟩ : Fin n)
      simp [hzero] at hcover0
      norm_num at hcover0
    obtain ⟨strictSupport, hstrictPositive⟩ := hpositive
    have htermLe (support : Finset (Fin n)) :
        (((2 * support.card : ℕ) : ℚ) * w support) ≤
          (n : ℚ) * w support := by
      by_cases hw : w support = 0
      · simp [hw]
      · apply mul_le_mul_of_nonneg_right _ (hnonneg support)
        exact_mod_cast (hsmall support hw).le
    have htermLt :
        (((2 * strictSupport.card : ℕ) : ℚ) * w strictSupport) <
          (n : ℚ) * w strictSupport := by
      apply mul_lt_mul_of_pos_right _ hstrictPositive
      exact_mod_cast hsmall strictSupport hstrictPositive.ne'
    have hsumStrict :
        (∑ support : Finset (Fin n),
            ((2 * support.card : ℕ) : ℚ) * w support) <
          ∑ support : Finset (Fin n), (n : ℚ) * w support := by
      exact Finset.sum_lt_sum (fun support _ ↦ htermLe support)
        ⟨strictSupport, Finset.mem_univ _, htermLt⟩
    have hincidence :
        (n : ℚ) ≤ ∑ support : Finset (Fin n),
          (support.card : ℚ) * w support := by
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
    have hscaledStrict :
        (2 : ℚ) * (∑ support : Finset (Fin n),
            (support.card : ℚ) * w support) <
          (n : ℚ) * ∑ support : Finset (Fin n), w support := by
      calc
        (2 : ℚ) * (∑ support : Finset (Fin n),
            (support.card : ℚ) * w support) =
            ∑ support : Finset (Fin n),
              ((2 * support.card : ℕ) : ℚ) * w support := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro support _
                push_cast
                ring
        _ < ∑ support : Finset (Fin n), (n : ℚ) * w support := hsumStrict
        _ = (n : ℚ) * ∑ support : Finset (Fin n), w support := by
          rw [Finset.mul_sum]
    have hincidenceScaled :
        (2 : ℚ) * n ≤ (2 : ℚ) *
          ∑ support : Finset (Fin n), (support.card : ℚ) * w support :=
      mul_le_mul_of_nonneg_left hincidence (by norm_num)
    have htotalScaled :
        (n : ℚ) * ∑ support : Finset (Fin n), w support ≤ (n : ℚ) * 2 :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    linarith

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
