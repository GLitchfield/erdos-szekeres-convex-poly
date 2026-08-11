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
