module

public import ErdosSzekeres.StructuralChargingResidualEscape567

@[expose] public section

/-!
# Thirty residual probes at state 567

Every seven-subset of a ten-point residual avoiding strong seven-sets contains
a bad six-subset.  Double-counting seven-set/bad-six incidences then gives at
least thirty bad six-subsets: there are `120` seven-subsets, while each fixed
six-subset lies in exactly four of them.
-/

namespace ErdosSzekeres

/-- The six-subsets of a residual which are not strong polygons. -/
noncomputable def BadResidualSixSets567 {n : ℕ} (χ : TripleColoring n)
    (residual : Finset (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact (residual.powersetCard 6).filter fun six ↦ ¬IsStrongPolygonSet χ six

/-- Seven-subsets of `residual` containing a fixed six-subset. -/
private def sevenSupersets567 {n : ℕ} (residual six : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (residual.powersetCard 7).filter fun seven ↦ six ⊆ seven

/-- A six-subset of a ten-set lies in exactly four seven-subsets. -/
private theorem card_sevenSupersets567
    {n : ℕ} {residual six : Finset (Fin n)}
    (hresidualCard : residual.card = 10)
    (hsixSub : six ⊆ residual) (hsixCard : six.card = 6) :
    (sevenSupersets567 residual six).card = 4 := by
  have hfamily :
      sevenSupersets567 residual six =
        (residual \ six).image (fun x ↦ insert x six) := by
    ext seven
    simp only [sevenSupersets567, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.mem_image]
    constructor
    · rintro ⟨⟨hsevenSub, hsevenCard⟩, hsixSeven⟩
      have hdiffCard : (seven \ six).card = 1 := by
        rw [Finset.card_sdiff_of_subset hsixSeven, hsevenCard, hsixCard]
      obtain ⟨x, hdiff⟩ := Finset.card_eq_one.mp hdiffCard
      have hxDiff : x ∈ seven \ six := by
        rw [hdiff]
        simp
      refine ⟨x, ?_, ?_⟩
      · exact Finset.mem_sdiff.mpr
          ⟨hsevenSub (Finset.mem_sdiff.mp hxDiff).1,
            (Finset.mem_sdiff.mp hxDiff).2⟩
      · rw [← Finset.sdiff_union_of_subset hsixSeven, hdiff]
        simp
    · rintro ⟨x, hx, rfl⟩
      have hxResidual : x ∈ residual := (Finset.mem_sdiff.mp hx).1
      have hxSix : x ∉ six := (Finset.mem_sdiff.mp hx).2
      exact ⟨⟨Finset.insert_subset hxResidual hsixSub, by
        rw [Finset.card_insert_of_notMem hxSix, hsixCard]⟩,
        Finset.subset_insert x six⟩
  rw [hfamily, Finset.card_image_iff.mpr]
  · rw [Finset.card_sdiff_of_subset hsixSub, hresidualCard, hsixCard]
  · intro x hx y _hy hxy
    exact (Finset.insert_inj (Finset.mem_sdiff.mp hx).2).mp hxy

/-- A ten-point residual without a strong seven-set contains at least thirty
bad six-subsets. -/
theorem thirty_le_card_badResidualSixSets567
    {n : ℕ} {χ : TripleColoring n} {residual : Finset (Fin n)}
    (hresidualCard : residual.card = 10)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ residual 7) :
    30 ≤ (BadResidualSixSets567 χ residual).card := by
  classical
  have hcover :
      residual.powersetCard 7 ⊆
        (BadResidualSixSets567 χ residual).biUnion
          (sevenSupersets567 residual) := by
    intro seven hseven
    have hsevenData := Finset.mem_powersetCard.mp hseven
    have hsevenNotStrong : ¬IsStrongPolygonSet χ seven := by
      intro hstrong
      exact hnoStrongSeven ⟨seven, hsevenData.1, hsevenData.2, hstrong⟩
    obtain ⟨six, hsixSub, hsixCard, hsixNotStrong⟩ :=
      exists_nonStrong_six_subset_of_notStrong_seven hsevenData.2
        hsevenNotStrong
    apply Finset.mem_biUnion.mpr
    refine ⟨six, ?_, ?_⟩
    · change six ∈ (residual.powersetCard 6).filter
        (fun candidate ↦ ¬IsStrongPolygonSet χ candidate)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr
          ⟨hsixSub.trans hsevenData.1, hsixCard⟩, hsixNotStrong⟩
    · exact Finset.mem_filter.mpr ⟨hseven, hsixSub⟩
  have hincidence :
      120 ≤ (BadResidualSixSets567 χ residual).card * 4 := by
    calc
      120 = (residual.powersetCard 7).card := by
        rw [Finset.card_powersetCard, hresidualCard]
        norm_num [Nat.choose]
      _ ≤ ((BadResidualSixSets567 χ residual).biUnion
          (sevenSupersets567 residual)).card := Finset.card_le_card hcover
      _ ≤ (BadResidualSixSets567 χ residual).card * 4 := by
        apply Finset.card_biUnion_le_card_mul
        intro six hsix
        change six ∈ (residual.powersetCard 6).filter
          (fun candidate ↦ ¬IsStrongPolygonSet χ candidate) at hsix
        have hsixData := Finset.mem_filter.mp hsix
        exact (card_sevenSupersets567 hresidualCard
          (Finset.mem_powersetCard.mp hsixData.1).1
          (Finset.mem_powersetCard.mp hsixData.1).2).le
  omega

/-- Four-block probes whose complementary residual six-set is not strong. -/
noncomputable def BadResidualFourBlocks567 {n : ℕ} (χ : TripleColoring n)
    (residual : Finset (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact (residual.powersetCard 4).filter fun block ↦
    ¬IsStrongPolygonSet χ (residual \ block)

/-- Complementing bad six-sets injects them into bad four-block probes. -/
theorem card_badResidualSixSets567_le_card_badResidualFourBlocks567
    {n : ℕ} {χ : TripleColoring n} {residual : Finset (Fin n)}
    (hresidualCard : residual.card = 10) :
    (BadResidualSixSets567 χ residual).card ≤
      (BadResidualFourBlocks567 χ residual).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun six ↦ residual \ six)
  · intro six hsix
    change six ∈ (residual.powersetCard 6).filter
      (fun candidate ↦ ¬IsStrongPolygonSet χ candidate) at hsix
    have hsixData := Finset.mem_filter.mp hsix
    have hsixPowerset := Finset.mem_powersetCard.mp hsixData.1
    change residual \ six ∈ (residual.powersetCard 4).filter
      (fun block ↦ ¬IsStrongPolygonSet χ (residual \ block))
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · exact Finset.sdiff_subset
      · rw [Finset.card_sdiff_of_subset hsixPowerset.1,
          hresidualCard, hsixPowerset.2]
    · rw [Finset.sdiff_sdiff_eq_self hsixPowerset.1]
      exact hsixData.2
  · intro six₁ hsix₁ six₂ hsix₂ hcomplements
    change six₁ ∈ (residual.powersetCard 6).filter
      (fun candidate ↦ ¬IsStrongPolygonSet χ candidate) at hsix₁
    change six₂ ∈ (residual.powersetCard 6).filter
      (fun candidate ↦ ¬IsStrongPolygonSet χ candidate) at hsix₂
    have hsix₁Sub :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hsix₁).1).1
    have hsix₂Sub :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hsix₂).1).1
    change residual \ six₁ = residual \ six₂ at hcomplements
    calc
      six₁ = residual \ (residual \ six₁) :=
        (Finset.sdiff_sdiff_eq_self hsix₁Sub).symm
      _ = residual \ (residual \ six₂) := congrArg (residual \ ·) hcomplements
      _ = six₂ := Finset.sdiff_sdiff_eq_self hsix₂Sub

/-- Strong-seven avoidance yields at least thirty complementary four-block
probes in a ten-point residual. -/
theorem thirty_le_card_badResidualFourBlocks567
    {n : ℕ} {χ : TripleColoring n} {residual : Finset (Fin n)}
    (hresidualCard : residual.card = 10)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ residual 7) :
    30 ≤ (BadResidualFourBlocks567 χ residual).card := by
  exact (thirty_le_card_badResidualSixSets567 hresidualCard hnoStrongSeven).trans
    (card_badResidualSixSets567_le_card_badResidualFourBlocks567
      hresidualCard)

/-- Deletion packing turns all thirty bad residual probes into strong-six
escapes meeting at least one of the two designated carriers. -/
theorem PackedInternalPairFourResidualEscape.exists_thirty_carrierTouching_probes
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7)
    {a b : Fin n} (ha : a ∈ first) (hb : b ∈ second) :
    ∃ probes : Finset (Finset (Fin n)),
      30 ≤ probes.card ∧
        ∀ block ∈ probes,
          block ⊆ ambient \ (first ∪ second) ∧ block.card = 4 ∧
            ¬IsStrongPolygonSet χ
              ((ambient \ (first ∪ second)) \ block) ∧
            ∃ third : Finset (Fin n),
              third ⊆ ambient \ insert a (insert b block) ∧
                third.card = 6 ∧ IsStrongPolygonSet χ third ∧
                  (HasPairEscapeOccupancy first second third .oneCarrier ∨
                    HasPairEscapeOccupancy first second third .twoCarrier) := by
  classical
  let residual := ambient \ (first ∪ second)
  have hnoStrongResidual : ¬ContainsStrongPolygonSet χ residual 7 := by
    intro hstrong
    exact hnoStrongSeven
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.sdiff_subset)
  refine ⟨BadResidualFourBlocks567 χ residual,
    thirty_le_card_badResidualFourBlocks567 hescape.1 hnoStrongResidual, ?_⟩
  intro block hblock
  change block ∈ (residual.powersetCard 4).filter
    (fun candidate ↦ ¬IsStrongPolygonSet χ (residual \ candidate)) at hblock
  have hblockData := Finset.mem_filter.mp hblock
  have hblockPowerset := Finset.mem_powersetCard.mp hblockData.1
  obtain ⟨third, hthirdSub, hthirdCard, hthirdStrong, hoccupancy⟩ :=
    hescape.exists_carrierTouching_witness ha hb hblockPowerset.1
      hblockPowerset.2 hblockData.2
  exact ⟨hblockPowerset.1, hblockPowerset.2, hblockData.2,
    third, hthirdSub, hthirdCard, hthirdStrong, hoccupancy⟩

end ErdosSzekeres
