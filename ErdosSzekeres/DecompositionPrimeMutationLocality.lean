module

public import ErdosSzekeres.DecompositionPrimeMutationRank
public import Mathlib.Data.Finset.SymmDiff

@[expose] public section

/-!
# Locality of decomposition-prime cores under a triple mutation

Recursive decomposition of a support depends only on triples wholly contained
in that support. Consequently, changing one ordered triple can alter prime-core
membership only for supports containing all three of its vertices. This is the
first structural reduction needed by mutation-rank approaches to Layer F.
-/

open scoped symmDiff

namespace ErdosSzekeres

/-- Two triple colorings agree on every ordered triple wholly supported by
`support`. -/
def TripleColoring.AgreeOnTriples {n : ℕ}
    (χ ψ : TripleColoring n) (support : Finset (Fin n)) : Prop :=
  ∀ t, t.i ∈ support → t.j ∈ support → t.k ∈ support → χ t = ψ t

/-- The three vertices used by an ordered triple. -/
def OrderedTriple.support {n : ℕ} (t : OrderedTriple n) : Finset (Fin n) :=
  {t.i, t.j, t.k}

/-- A deep-below split is unchanged when the two colorings agree on its
support. -/
theorem HasDeepBelowSplit.of_agreeOnTriples
    {n : ℕ} {χ ψ : TripleColoring n} {lower upper : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper)
    (hagree : χ.AgreeOnTriples ψ (lower ∪ upper)) :
    HasDeepBelowSplit ψ lower upper := by
  refine ⟨h.disjoint, ?_⟩
  intro t hi hj hk hnotLower hnotUpper
  calc
    ψ t = χ t := (hagree t hi hj hk).symm
    _ = if t.j ∈ lower then Turn.left else Turn.right :=
      h.crossing t hi hj hk hnotLower hnotUpper

/-- Recursive decomposability transfers between colorings that agree on the
entire support. -/
theorem IsDecomposableOn.of_agreeOnTriples
    {n : ℕ} {χ ψ : TripleColoring n} {support : Finset (Fin n)}
    (h : IsDecomposableOn χ support)
    (hagree : χ.AgreeOnTriples ψ support) :
    IsDecomposableOn ψ support := by
  induction h with
  | singleton i => exact .singleton i
  | @split lower upper hlower hupper hdeep ihlower ihupper =>
      exact .split
        (ihlower fun t hi hj hk ↦ hagree t
          (Finset.mem_union_left upper hi)
          (Finset.mem_union_left upper hj)
          (Finset.mem_union_left upper hk))
        (ihupper fun t hi hj hk ↦ hagree t
          (Finset.mem_union_right lower hi)
          (Finset.mem_union_right lower hj)
          (Finset.mem_union_right lower hk))
        (hdeep.of_agreeOnTriples hagree)

/-- Decomposability on a fixed support depends only on the colors of triples
inside that support. -/
theorem isDecomposableOn_congr_of_agreeOnTriples
    {n : ℕ} {χ ψ : TripleColoring n} {support : Finset (Fin n)}
    (hagree : χ.AgreeOnTriples ψ support) :
    IsDecomposableOn χ support ↔ IsDecomposableOn ψ support := by
  constructor
  · exact fun h ↦ h.of_agreeOnTriples hagree
  · exact fun h ↦ h.of_agreeOnTriples fun t hi hj hk ↦
      (hagree t hi hj hk).symm

/-- The existence of a proper root split on a fixed support depends only on
the colors of triples inside that support. -/
theorem hasProperDeepBelowSplitOn_congr_of_agreeOnTriples
    {n : ℕ} {χ ψ : TripleColoring n} {support : Finset (Fin n)}
    (hagree : χ.AgreeOnTriples ψ support) :
    HasProperDeepBelowSplitOn χ support ↔
      HasProperDeepBelowSplitOn ψ support := by
  constructor <;>
    rintro ⟨lower, upper, hlower, hupper, hunion, hdeep⟩
  · refine ⟨lower, upper, hlower, hupper, hunion, ?_⟩
    apply hdeep.of_agreeOnTriples
    simpa [hunion] using hagree
  · refine ⟨lower, upper, hlower, hupper, hunion, ?_⟩
    apply hdeep.of_agreeOnTriples
    simpa [hunion] using fun t hi hj hk ↦ (hagree t hi hj hk).symm

/-- Decomposition-primality on a fixed support depends only on the colors of
triples inside that support. -/
theorem isDecompositionPrimeOn_congr_of_agreeOnTriples
    {n : ℕ} {χ ψ : TripleColoring n} {support : Finset (Fin n)}
    (hagree : χ.AgreeOnTriples ψ support) :
    IsDecompositionPrimeOn χ support ↔
      IsDecompositionPrimeOn ψ support := by
  simp only [IsDecompositionPrimeOn]
  rw [hasProperDeepBelowSplitOn_congr_of_agreeOnTriples hagree]

/-- Away from the changed triple, a single mutation leaves all supported
triple colors unchanged. -/
theorem SingleTripleMutation.agreeOnTriples_of_not_support_subset
    {n : ℕ} {χ ψ : TripleColoring n} {support : Finset (Fin n)}
    {changed : OrderedTriple n}
    (hmut : χ changed ≠ ψ changed ∧
      ∀ u, u ≠ changed → χ u = ψ u)
    (houtside : ¬changed.support ⊆ support) :
    χ.AgreeOnTriples ψ support := by
  intro u hi hj hk
  apply hmut.2
  intro hueq
  subst u
  apply houtside
  intro x hx
  simp only [OrderedTriple.support, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx
  · simpa [hx] using hi
  · simpa [hx] using hj
  · simpa [hx] using hk

/-- A single mutation supplies one changed triple and coloring agreement on
every support that omits at least one of its vertices. -/
theorem SingleTripleMutation.exists_changedTriple_with_locality
    {n : ℕ} {χ ψ : TripleColoring n}
    (hmut : SingleTripleMutation χ ψ) :
    ∃ changed : OrderedTriple n,
      χ changed ≠ ψ changed ∧
      ∀ support : Finset (Fin n),
        ¬changed.support ⊆ support → χ.AgreeOnTriples ψ support := by
  obtain ⟨changed, hchanged, hagree⟩ := hmut
  exact ⟨changed, hchanged, fun _ houtside ↦
    SingleTripleMutation.agreeOnTriples_of_not_support_subset
      ⟨hchanged, hagree⟩ houtside⟩

/-- A mutation cannot change whether a support is decomposition-prime unless
that support contains all three changed vertices. -/
theorem SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
    {n : ℕ} {χ ψ : TripleColoring n} {support : Finset (Fin n)}
    {changed : OrderedTriple n}
    (hmut : χ changed ≠ ψ changed ∧
      ∀ u, u ≠ changed → χ u = ψ u)
    (houtside : ¬changed.support ⊆ support) :
    IsDecompositionPrimeOn χ support ↔
      IsDecompositionPrimeOn ψ support := by
  apply isDecompositionPrimeOn_congr_of_agreeOnTriples
  exact SingleTripleMutation.agreeOnTriples_of_not_support_subset
    hmut houtside

/-- Direct prime-core locality for a single mutation: every support that omits
one changed vertex has identical prime status before and after the mutation. -/
theorem SingleTripleMutation.exists_primeCore_locality
    {n : ℕ} {χ ψ : TripleColoring n}
    (hmut : SingleTripleMutation χ ψ) :
    ∃ changed : OrderedTriple n,
      χ changed ≠ ψ changed ∧
      ∀ support : Finset (Fin n),
        ¬changed.support ⊆ support →
          (IsDecompositionPrimeOn χ support ↔
            IsDecompositionPrimeOn ψ support) := by
  obtain ⟨changed, hchanged, hagree⟩ := hmut
  exact ⟨changed, hchanged, fun _ houtside ↦
    SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
      ⟨hchanged, hagree⟩ houtside⟩

/-- The symmetric difference of the prime-core families is contained in the
family of supports carrying all three changed vertices. -/
theorem SingleTripleMutation.decompositionPrimeCores_symmDiff_subset
    {n : ℕ} {χ ψ : TripleColoring n} {changed : OrderedTriple n}
    (hmut : χ changed ≠ ψ changed ∧
      ∀ u, u ≠ changed → χ u = ψ u) :
    decompositionPrimeCores χ ∆ decompositionPrimeCores ψ ⊆
      Finset.univ.powerset.filter fun support ↦
        changed.support ⊆ support := by
  intro support hsymm
  have hsubset : changed.support ⊆ support := by
    by_contra houtside
    have hprime :=
      SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
        hmut houtside
    rw [Finset.mem_symmDiff] at hsymm
    rcases hsymm with hχ | hψ
    · exact hχ.2 (mem_decompositionPrimeCores_iff.mpr
        (hprime.mp (mem_decompositionPrimeCores_iff.mp hχ.1)))
    · exact hψ.2 (mem_decompositionPrimeCores_iff.mpr
        (hprime.mpr (mem_decompositionPrimeCores_iff.mp hψ.1)))
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ support), hsubset⟩

/-- Prime cores present before a mutation but absent afterward. -/
noncomputable def destroyedPrimeCores {n : ℕ}
    (χ ψ : TripleColoring n) : Finset (Finset (Fin n)) :=
  decompositionPrimeCores χ \ decompositionPrimeCores ψ

/-- Prime cores absent before a mutation but present afterward. -/
noncomputable def createdPrimeCores {n : ℕ}
    (χ ψ : TripleColoring n) : Finset (Finset (Fin n)) :=
  decompositionPrimeCores ψ \ decompositionPrimeCores χ

/-- The change in the raw prime-core count is exactly the balance between
destroyed and newly created prime cores. -/
theorem primeCoreCount_add_destroyed_eq_add_created
    {n : ℕ} (χ ψ : TripleColoring n) :
    PrimeCoreCount ψ + (destroyedPrimeCores χ ψ).card =
      PrimeCoreCount χ + (createdPrimeCores χ ψ).card := by
  classical
  have hχ := Finset.card_sdiff_add_card_inter
    (decompositionPrimeCores χ) (decompositionPrimeCores ψ)
  have hψ := Finset.card_sdiff_add_card_inter
    (decompositionPrimeCores ψ) (decompositionPrimeCores χ)
  simp only [PrimeCoreCount, destroyedPrimeCores, createdPrimeCores] at *
  rw [Finset.inter_comm] at hψ
  omega

/-- The raw rank decreases precisely when a mutation destroys more prime
cores than it creates. -/
theorem primeCoreCount_lt_iff_created_lt_destroyed
    {n : ℕ} (χ ψ : TripleColoring n) :
    PrimeCoreCount ψ < PrimeCoreCount χ ↔
      (createdPrimeCores χ ψ).card <
        (destroyedPrimeCores χ ψ).card := by
  classical
  simpa only [PrimeCoreCount, createdPrimeCores, destroyedPrimeCores] using
    (Finset.card_sdiff_lt_card_sdiff_iff
      (s := decompositionPrimeCores ψ)
      (t := decompositionPrimeCores χ)).symm

/-- The number of decomposition-prime restrictions having a specified
cardinality. This is one coordinate of the cardinality-stratified rank. -/
noncomputable def PrimeCoreCountAtCard {n : ℕ}
    (χ : TripleColoring n) (m : ℕ) : ℕ :=
  ((decompositionPrimeCores χ).filter fun support ↦
    support.card = m).card

/-- At every cardinality stratum, a single mutation can change prime-core
membership only on supports containing all three changed vertices. -/
theorem SingleTripleMutation.primeCoreStratum_symmDiff_subset
    {n m : ℕ} {χ ψ : TripleColoring n} {changed : OrderedTriple n}
    (hmut : χ changed ≠ ψ changed ∧
      ∀ u, u ≠ changed → χ u = ψ u) :
    ((decompositionPrimeCores χ).filter fun support ↦ support.card = m) ∆
        ((decompositionPrimeCores ψ).filter fun support ↦ support.card = m) ⊆
      Finset.univ.powerset.filter fun support ↦
        changed.support ⊆ support ∧ support.card = m := by
  intro support hsymm
  rw [Finset.mem_symmDiff] at hsymm
  have hcard : support.card = m := by
    rcases hsymm with hχ | hψ
    · exact (Finset.mem_filter.mp hχ.1).2
    · exact (Finset.mem_filter.mp hψ.1).2
  have hglobal :
      support ∈ decompositionPrimeCores χ ∆ decompositionPrimeCores ψ := by
    rw [Finset.mem_symmDiff]
    rcases hsymm with hχ | hψ
    · left
      refine ⟨(Finset.mem_filter.mp hχ.1).1, ?_⟩
      intro hψCore
      exact hχ.2 (Finset.mem_filter.mpr ⟨hψCore, hcard⟩)
    · right
      refine ⟨(Finset.mem_filter.mp hψ.1).1, ?_⟩
      intro hχCore
      exact hψ.2 (Finset.mem_filter.mpr ⟨hχCore, hcard⟩)
  have hcarrier :=
    SingleTripleMutation.decompositionPrimeCores_symmDiff_subset
      hmut hglobal
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ support),
      (Finset.mem_filter.mp hcarrier).2, hcard⟩

/-- A prime-core rank in which every core of cardinality `m` receives weight
`(2^n+1)^m`. The large base makes higher-cardinality strata dominate lower
ones in later comparison lemmas. -/
noncomputable def StratifiedPrimeCoreRank {n : ℕ}
    (χ : TripleColoring n) : ℕ :=
  ∑ support ∈ decompositionPrimeCores χ,
    (2 ^ n + 1) ^ support.card

/-- If the first changed cardinality stratum, read from largest to smallest,
loses a prime core, then the stratified rank strictly decreases.  The base
`2^n+1` makes the total contribution of every lower support too small to
cancel one lost core at the distinguished stratum. -/
theorem stratifiedPrimeCoreRank_lt_of_topStratumDrop
    {n m : ℕ} {χ ψ : TripleColoring n}
    (hm : 0 < m)
    (habove : ∀ support : Finset (Fin n), m < support.card →
      (support ∈ decompositionPrimeCores χ ↔
        support ∈ decompositionPrimeCores ψ))
    (hdrop : PrimeCoreCountAtCard ψ m < PrimeCoreCountAtCard χ m) :
    StratifiedPrimeCoreRank ψ < StratifiedPrimeCoreRank χ := by
  classical
  let base : ℕ := 2 ^ n + 1
  let weight : Finset (Fin n) → ℕ := fun support ↦ base ^ support.card
  let high (cores : Finset (Finset (Fin n))) :=
    cores.filter fun support ↦ m < support.card
  let same (cores : Finset (Finset (Fin n))) :=
    cores.filter fun support ↦ support.card = m
  let low (cores : Finset (Finset (Fin n))) :=
    cores.filter fun support ↦ support.card < m
  have split (cores : Finset (Finset (Fin n))) :
      ∑ support ∈ cores, weight support =
        (∑ support ∈ high cores, weight support) +
        (∑ support ∈ same cores, weight support) +
        ∑ support ∈ low cores, weight support := by
    have hfirst := Finset.sum_filter_add_sum_filter_not cores
      (fun support ↦ m < support.card) weight
    have hsecond := Finset.sum_filter_add_sum_filter_not
      (cores.filter fun support ↦ ¬m < support.card)
      (fun support ↦ support.card = m) weight
    have hsame :
        ((cores.filter fun support ↦ ¬m < support.card).filter
          fun support ↦ support.card = m) = same cores := by
      ext support
      simp [same]
      omega
    have hlow :
        ((cores.filter fun support ↦ ¬m < support.card).filter
          fun support ↦ ¬support.card = m) = low cores := by
      ext support
      simp only [Finset.mem_filter]
      unfold low
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hmem, hnotGreater⟩, hne⟩
        exact ⟨hmem, by omega⟩
      · rintro ⟨hmem, hlt⟩
        exact ⟨⟨hmem, by omega⟩, by omega⟩
    rw [hsame, hlow] at hsecond
    calc
      ∑ support ∈ cores, weight support =
          (∑ support ∈ cores.filter (fun support ↦ m < support.card),
            weight support) +
          ∑ support ∈ cores.filter (fun support ↦ ¬m < support.card),
            weight support := hfirst.symm
      _ = (∑ support ∈ high cores, weight support) +
          ((∑ support ∈ same cores, weight support) +
            ∑ support ∈ low cores, weight support) := by
        rw [hsecond]
      _ = (∑ support ∈ high cores, weight support) +
          (∑ support ∈ same cores, weight support) +
          ∑ support ∈ low cores, weight support := by omega
  have hhigh :
      high (decompositionPrimeCores χ) =
        high (decompositionPrimeCores ψ) := by
    ext support
    simp only [high, Finset.mem_filter]
    constructor
    · rintro ⟨hχ, hcard⟩
      exact ⟨(habove support hcard).mp hχ, hcard⟩
    · rintro ⟨hψ, hcard⟩
      exact ⟨(habove support hcard).mpr hψ, hcard⟩
  have hsameSum (cores : Finset (Finset (Fin n))) :
      ∑ support ∈ same cores, weight support =
        (same cores).card * base ^ m := by
    apply Finset.sum_const_nat
    intro support hsupport
    have hcard : support.card = m := (Finset.mem_filter.mp hsupport).2
    simp only [weight, hcard]
  have hlowCard :
      (low (decompositionPrimeCores ψ)).card ≤ 2 ^ n := by
    calc
      (low (decompositionPrimeCores ψ)).card ≤
          (Finset.univ.powerset : Finset (Finset (Fin n))).card :=
        Finset.card_le_card (by
          intro support _
          exact Finset.mem_powerset.mpr (Finset.subset_univ support))
      _ = 2 ^ n := by simp
  have hbasePos : 0 < base := by
    simp only [base]
    omega
  have hlowWeight : ∀ support ∈ low (decompositionPrimeCores ψ),
      weight support ≤ base ^ (m - 1) := by
    intro support hsupport
    have hcard : support.card < m := (Finset.mem_filter.mp hsupport).2
    simp only [weight]
    apply Nat.pow_le_pow_right hbasePos
    omega
  have hlowSum :
      ∑ support ∈ low (decompositionPrimeCores ψ), weight support <
        base ^ m := by
    have hsumCard :
        ∑ support ∈ low (decompositionPrimeCores ψ), weight support ≤
          (low (decompositionPrimeCores ψ)).card * base ^ (m - 1) := by
      simpa using Finset.sum_le_card_nsmul
        (low (decompositionPrimeCores ψ)) weight (base ^ (m - 1)) hlowWeight
    have hcardMul :
        (low (decompositionPrimeCores ψ)).card * base ^ (m - 1) ≤
          2 ^ n * base ^ (m - 1) :=
      Nat.mul_le_mul_right (base ^ (m - 1)) hlowCard
    have hbaseLt : 2 ^ n < base := by
      simp only [base]
      omega
    have hpowPos : 0 < base ^ (m - 1) := by positivity
    have hmulLt :
        2 ^ n * base ^ (m - 1) < base * base ^ (m - 1) :=
      Nat.mul_lt_mul_of_pos_right hbaseLt hpowPos
    calc
      ∑ support ∈ low (decompositionPrimeCores ψ), weight support ≤
          (low (decompositionPrimeCores ψ)).card * base ^ (m - 1) := hsumCard
      _ ≤ 2 ^ n * base ^ (m - 1) := hcardMul
      _ < base * base ^ (m - 1) := hmulLt
      _ = base ^ m := by
        rw [Nat.mul_comm, ← Nat.pow_succ]
        congr
        omega
  have hdrop' :
      (same (decompositionPrimeCores ψ)).card <
        (same (decompositionPrimeCores χ)).card := hdrop
  simp only [StratifiedPrimeCoreRank]
  change (∑ support ∈ decompositionPrimeCores ψ, weight support) <
    ∑ support ∈ decompositionPrimeCores χ, weight support
  have hsplitψ := split (decompositionPrimeCores ψ)
  have hsplitχ := split (decompositionPrimeCores χ)
  rw [hsplitψ, hsplitχ, hhigh, hsameSum, hsameSum]
  have hstep :
      (same (decompositionPrimeCores ψ)).card + 1 ≤
        (same (decompositionPrimeCores χ)).card := by omega
  have hpowPos : 0 < base ^ m := by positivity
  have hmiddle :
      (same (decompositionPrimeCores ψ)).card * base ^ m + base ^ m ≤
        (same (decompositionPrimeCores χ)).card * base ^ m := by
    simpa [Nat.add_mul] using Nat.mul_le_mul_right (base ^ m) hstep
  omega

/-- The geometric obligation for the stratified Layer-F route: above the
exact threshold, every target-free realizable nondecomposable coloring has an
at-most-three-mutation endpoint whose highest changed prime-core stratum
strictly decreases.  Intermediate ranks are intentionally unconstrained. -/
def ThreeStepTopPrimeStratumDropsAboveAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}, 2 ^ (k - 2) < n →
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ¬IsDecomposable χ →
    ∃ ψ m,
      AtMostThree (TargetFreeRealizableMutationStepAt k) χ ψ ∧
      0 < m ∧
      (∀ support : Finset (Fin n), m < support.card →
        (support ∈ decompositionPrimeCores χ ↔
          support ∈ decompositionPrimeCores ψ)) ∧
      PrimeCoreCountAtCard ψ m < PrimeCoreCountAtCard χ m

/-- A top-stratum mutation macro supplies the concrete natural-valued rank
descent required by the normalization theorem. -/
theorem threeStepMutationRankDescendsAbove_of_topPrimeStratumDrop
    {k : ℕ} (hdrop : ThreeStepTopPrimeStratumDropsAboveAt k) :
    ThreeStepMutationRankDescendsAboveAt k
      (fun _ χ ↦ StratifiedPrimeCoreRank χ) := by
  intro n χ hcard hrealizable htarget hindecomposable
  obtain ⟨ψ, m, hpath, hm, habove, hcount⟩ :=
    hdrop hcard hrealizable htarget hindecomposable
  exact ⟨ψ, hpath,
    stratifiedPrimeCoreRank_lt_of_topStratumDrop hm habove hcount⟩

/-- On a nonempty ground set, the stratified rank vanishes exactly at the
recursively decomposable colorings. -/
theorem stratifiedPrimeCoreRank_eq_zero_iff
    {n : ℕ} {χ : TripleColoring n} (hn : 0 < n) :
    StratifiedPrimeCoreRank χ = 0 ↔ IsDecomposable χ := by
  rw [← primeCoreCount_eq_zero_iff hn]
  simp only [StratifiedPrimeCoreRank, PrimeCoreCount]
  constructor
  · intro hzero
    apply Finset.card_eq_zero.mpr
    by_contra hne
    have hnonempty : (decompositionPrimeCores χ).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨support, hsupport⟩ := hnonempty
    have hpos : 0 < (2 ^ n + 1) ^ support.card := by positivity
    have hle : (2 ^ n + 1) ^ support.card ≤
        ∑ support ∈ decompositionPrimeCores χ,
          (2 ^ n + 1) ^ support.card := by
      simpa only using Finset.single_le_sum
        (s := decompositionPrimeCores χ)
        (f := fun support ↦ (2 ^ n + 1) ^ support.card)
        (fun _ _ ↦ Nat.zero_le _) hsupport
    omega
  · intro hzero
    simp only [Finset.card_eq_zero.mp hzero, Finset.sum_empty]

end ErdosSzekeres

end
