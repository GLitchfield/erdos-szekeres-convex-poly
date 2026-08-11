module

public import ErdosSzekeres.StructuralChargingResidualEscape
public import ErdosSzekeres.StructuralChargingWitnessBranchesPacked
public import ErdosSzekeres.StrongPredecessorBicoloring

@[expose] public section

/-!
# State-567 specialization of the uniform residual escape

This file proves that the generic deletion-packing theorem reproduces the
existing sharp 22-point normalization.
-/

namespace ErdosSzekeres

/-- A non-strong seven-set contains a non-strong six-subset.  This is the
contrapositive form of the generic predecessor-locality theorem. -/
theorem exists_nonStrong_six_subset_of_notStrong_seven
    {n : ℕ} {χ : TripleColoring n} {seven : Finset (Fin n)}
    (hsevenCard : seven.card = 7)
    (hsevenNotStrong : ¬IsStrongPolygonSet χ seven) :
    ∃ six : Finset (Fin n), six ⊆ seven ∧ six.card = 6 ∧
      ¬IsStrongPolygonSet χ six := by
  by_contra hnone
  apply hsevenNotStrong
  apply isStrongPolygonSet_of_all_pred_subsets (k := 7) (by omega)
    hsevenCard
  intro six hsixSub hsixCard
  by_contra hsixNotStrong
  exact hnone ⟨six, hsixSub, by simpa using hsixCard, hsixNotStrong⟩

/-- A ten-set avoiding strong seven-sets has two distinct non-strong
six-subsets.  The second seven-set is chosen after erasing a vertex of the
first bad six-set, which forces the two witnesses to differ. -/
theorem exists_two_nonStrong_six_subsets_of_card_ten
    {n : ℕ} {χ : TripleColoring n} {residual : Finset (Fin n)}
    (hresidualCard : residual.card = 10)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ residual 7) :
    ∃ six₁ six₂ : Finset (Fin n),
      six₁ ⊆ residual ∧ six₁.card = 6 ∧ ¬IsStrongPolygonSet χ six₁ ∧
      six₂ ⊆ residual ∧ six₂.card = 6 ∧ ¬IsStrongPolygonSet χ six₂ ∧
      six₁ ≠ six₂ := by
  obtain ⟨seven₁, hseven₁Sub, hseven₁Card⟩ :=
    Finset.exists_subset_card_eq (show 7 ≤ residual.card by omega)
  have hseven₁NotStrong : ¬IsStrongPolygonSet χ seven₁ := by
    intro hstrong
    exact hnoStrongSeven ⟨seven₁, hseven₁Sub, hseven₁Card, hstrong⟩
  obtain ⟨six₁, hsix₁SubSeven, hsix₁Card, hsix₁NotStrong⟩ :=
    exists_nonStrong_six_subset_of_notStrong_seven hseven₁Card
      hseven₁NotStrong
  have hsix₁Sub : six₁ ⊆ residual := hsix₁SubSeven.trans hseven₁Sub
  obtain ⟨x, hxSix₁⟩ : six₁.Nonempty :=
    Finset.card_pos.mp (show 0 < six₁.card by omega)
  have hxResidual : x ∈ residual := hsix₁Sub hxSix₁
  have herasedCard : (residual.erase x).card = 9 := by
    rw [Finset.card_erase_of_mem hxResidual, hresidualCard]
  obtain ⟨seven₂, hseven₂SubErase, hseven₂Card⟩ :=
    Finset.exists_subset_card_eq (show 7 ≤ (residual.erase x).card by omega)
  have hseven₂Sub : seven₂ ⊆ residual :=
    hseven₂SubErase.trans (Finset.erase_subset _ _)
  have hseven₂NotStrong : ¬IsStrongPolygonSet χ seven₂ := by
    intro hstrong
    exact hnoStrongSeven ⟨seven₂, hseven₂Sub, hseven₂Card, hstrong⟩
  obtain ⟨six₂, hsix₂SubSeven, hsix₂Card, hsix₂NotStrong⟩ :=
    exists_nonStrong_six_subset_of_notStrong_seven hseven₂Card
      hseven₂NotStrong
  have hsix₂Sub : six₂ ⊆ residual := hsix₂SubSeven.trans hseven₂Sub
  have hxNotSeven₂ : x ∉ seven₂ := by
    intro hxSeven₂
    exact (Finset.mem_erase.mp (hseven₂SubErase hxSeven₂)).1 rfl
  have hsixNe : six₁ ≠ six₂ := by
    intro heq
    apply hxNotSeven₂
    apply hsix₂SubSeven
    rw [← heq]
    exact hxSix₁
  exact ⟨six₁, six₂, hsix₁Sub, hsix₁Card, hsix₁NotStrong,
    hsix₂Sub, hsix₂Card, hsix₂NotStrong, hsixNe⟩

/-- Complementing two bad six-subsets of a ten-point residual gives two
distinct four-block probes whose unused residual six-sets are non-strong. -/
theorem exists_two_fourBlocks_with_nonStrong_residual_complements
    {n : ℕ} {χ : TripleColoring n}
    {ambient residual : Finset (Fin n)}
    (hresidualSub : residual ⊆ ambient)
    (hresidualCard : residual.card = 10)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7) :
    ∃ block₁ block₂ : Finset (Fin n),
      block₁ ⊆ residual ∧ block₁.card = 4 ∧
      block₂ ⊆ residual ∧ block₂.card = 4 ∧
      block₁ ≠ block₂ ∧
      ¬IsStrongPolygonSet χ (residual \ block₁) ∧
      ¬IsStrongPolygonSet χ (residual \ block₂) := by
  have hnoStrongResidual : ¬ContainsStrongPolygonSet χ residual 7 := by
    intro hstrong
    exact hnoStrongSeven
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hresidualSub)
  obtain ⟨six₁, six₂, hsix₁Sub, hsix₁Card, hsix₁NotStrong,
      hsix₂Sub, hsix₂Card, hsix₂NotStrong, hsixNe⟩ :=
    exists_two_nonStrong_six_subsets_of_card_ten hresidualCard
      hnoStrongResidual
  let block₁ := residual \ six₁
  let block₂ := residual \ six₂
  have hblock₁Sub : block₁ ⊆ residual := Finset.sdiff_subset
  have hblock₂Sub : block₂ ⊆ residual := Finset.sdiff_subset
  have hblock₁Card : block₁.card = 4 := by
    simp only [block₁]
    rw [Finset.card_sdiff_of_subset hsix₁Sub, hresidualCard, hsix₁Card]
  have hblock₂Card : block₂.card = 4 := by
    simp only [block₂]
    rw [Finset.card_sdiff_of_subset hsix₂Sub, hresidualCard, hsix₂Card]
  have hcomplement₁ : residual \ block₁ = six₁ := by
    ext x
    simp only [block₁, Finset.mem_sdiff]
    constructor
    · intro hx
      by_contra hxSix
      exact hx.2 ⟨hx.1, hxSix⟩
    · intro hx
      exact ⟨hsix₁Sub hx, fun hxResidualSix ↦ hxResidualSix.2 hx⟩
  have hcomplement₂ : residual \ block₂ = six₂ := by
    ext x
    simp only [block₂, Finset.mem_sdiff]
    constructor
    · intro hx
      by_contra hxSix
      exact hx.2 ⟨hx.1, hxSix⟩
    · intro hx
      exact ⟨hsix₂Sub hx, fun hxResidualSix ↦ hxResidualSix.2 hx⟩
  have hblockNe : block₁ ≠ block₂ := by
    intro hblocks
    apply hsixNe
    rw [← hcomplement₁, ← hcomplement₂, hblocks]
  exact ⟨block₁, block₂, hblock₁Sub, hblock₁Card,
    hblock₂Sub, hblock₂Card, hblockNe,
    hcomplement₁ ▸ hsix₁NotStrong, hcomplement₂ ▸ hsix₂NotStrong⟩

/-- The certified `(5,6,6)` one-change theorem is the predecessor state which
produces deletion packing at state 567. -/
theorem oneChangeStateUpper_566 : OneChangeStateUpper 5 6 6 := by
  intro n χ support hone hcard
  have hcardSixteen : 16 ≤ support.card := by
    simpa using hcard
  exact containsCapFive_or_cupSix_or_strongSix_of_oneChange_card_ge_sixteen
    hone hcardSixteen

/-- The existing sharp strong-six packing theorem is an instance of the
uniform one-change-state packing consumer. -/
theorem strongSixAvoidsEverySix_of_card_ge_twenty_two_via_state
    {n : ℕ} {χ : TripleColoring n} {ambient : Finset (Fin n)}
    (hone : OneChangeOn χ ambient) (hcard : 22 ≤ ambient.card)
    (hnoCap : ¬ContainsCapSet χ ambient 5)
    (hnoCup : ¬ContainsCupSet χ ambient 6) :
    StrongSixAvoidsEverySix χ ambient := by
  rw [← strongPolygonAvoidsEveryDeletion_six_iff]
  apply strongPolygonAvoidsEveryDeletion_of_oneChangeStateUpper
    oneChangeStateUpper_566 hone
  · simpa using hcard
  · exact hnoCap
  · exact hnoCup

/-- The full packed internal-pair hypotheses feed the parameter-uniform
residual-escape theorem at `(carrier,residual,block,witness) = (6,10,4,6)`. -/
theorem packedInternalPair_has_fourResidualEscape_via_generic
    {n : ℕ} {χ : TripleColoring n}
    {left right first second : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (htotal : left.card + right.card = 22)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hfirstSide : first ⊆ left ∨ first ⊆ right)
    (hsecondSub : second ⊆ left ∪ right)
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second) :
    PackedInternalPairFourResidualEscape χ (left ∪ right) first second := by
  have hfirstSub : first ⊆ left ∪ right :=
    hfirstSide.elim
      (fun h ↦ h.trans Finset.subset_union_left)
      (fun h ↦ h.trans Finset.subset_union_right)
  have hambientCard : (left ∪ right).card = 6 + 6 + 10 := by
    rw [Finset.card_union_of_disjoint hdisjoint]
    omega
  have hgeneric := pairResidualEscape_of_avoidsEveryDeletion
    (carrierCard := 6) (residualCard := 10) (blockCard := 4)
    (witnessCard := 6) hambientCard hfirstSub hsecondSub hmutual.1
    hmutual.2.1 hmutual.2.2.1
    ((strongPolygonAvoidsEveryDeletion_six_iff).2 hpacking)
  simpa [PairResidualEscape, PackedInternalPairFourResidualEscape] using hgeneric

/-- Every four-block probe has a concrete strong-six witness in one of the
three carrier occupancy classes. -/
theorem PackedInternalPairFourResidualEscape.exists_witness_with_occupancy
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block : Finset (Fin n)} {a b : Fin n}
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (ha : a ∈ first) (hb : b ∈ second)
    (hblockSub : block ⊆ ambient \ (first ∪ second))
    (hblockCard : block.card = 4) :
    ∃ third : Finset (Fin n),
      third ⊆ ambient \ insert a (insert b block) ∧
        third.card = 6 ∧ IsStrongPolygonSet χ third ∧
          ∃ occupancy, HasPairEscapeOccupancy first second third occupancy := by
  have hgeneric : PairResidualEscape χ ambient first second 10 4 6 := by
    simpa [PairResidualEscape, PackedInternalPairFourResidualEscape] using hescape
  obtain ⟨third, hthirdSub, hthirdCard, hthirdStrong⟩ :=
    hgeneric.exists_witness ha hb hblockSub hblockCard
  exact ⟨third, hthirdSub, hthirdCard, hthirdStrong,
    exists_pairEscapeOccupancy first second third⟩

/-- In the residual-only occupancy branch, a selected strong-six witness is
exactly the complement of the deleted four-block inside the ten-point
residual. -/
theorem packedResidualOnlyWitness_eq_residual_sdiff
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block third : Finset (Fin n)} {a b : Fin n}
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hblockSub : block ⊆ ambient \ (first ∪ second))
    (hblockCard : block.card = 4)
    (hthirdSub : third ⊆ ambient \ insert a (insert b block))
    (hthirdCard : third.card = 6)
    (hresidualOnly :
      HasPairEscapeOccupancy first second third .residualOnly) :
    third = (ambient \ (first ∪ second)) \ block := by
  change Disjoint third first ∧ Disjoint third second at hresidualOnly
  apply residualWitness_eq_residual_sdiff
    (residualCard := 10) (blockCard := 4) (witnessCard := 6)
    hescape.1 hblockSub hblockCard hthirdSub hthirdCard
    hresidualOnly.1 hresidualOnly.2
  norm_num

/-- If a selected residual complement is not strong, deletion packing cannot
return a residual-only witness.  The escape must meet one or both designated
carriers. -/
theorem PackedInternalPairFourResidualEscape.exists_carrierTouching_witness
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block : Finset (Fin n)} {a b : Fin n}
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (ha : a ∈ first) (hb : b ∈ second)
    (hblockSub : block ⊆ ambient \ (first ∪ second))
    (hblockCard : block.card = 4)
    (hcomplementNotStrong :
      ¬IsStrongPolygonSet χ ((ambient \ (first ∪ second)) \ block)) :
    ∃ third : Finset (Fin n),
      third ⊆ ambient \ insert a (insert b block) ∧
        third.card = 6 ∧ IsStrongPolygonSet χ third ∧
          (HasPairEscapeOccupancy first second third .oneCarrier ∨
            HasPairEscapeOccupancy first second third .twoCarrier) := by
  obtain ⟨third, hthirdSub, hthirdCard, hthirdStrong, occupancy, hoccupancy⟩ :=
    hescape.exists_witness_with_occupancy ha hb hblockSub hblockCard
  cases occupancy with
  | residualOnly =>
      have heq := packedResidualOnlyWitness_eq_residual_sdiff hescape
        hblockSub hblockCard hthirdSub hthirdCard hoccupancy
      exact (hcomplementNotStrong (heq ▸ hthirdStrong)).elim
  | oneCarrier =>
      exact ⟨third, hthirdSub, hthirdCard, hthirdStrong, Or.inl hoccupancy⟩
  | twoCarrier =>
      exact ⟨third, hthirdSub, hthirdCard, hthirdStrong, Or.inr hoccupancy⟩

/-- Strong-seven avoidance supplies two distinct residual probes whose packed
strong-six escapes both touch at least one designated carrier.  This removes
the residual-only terminal class from the exact state-567 branch. -/
theorem packedInternalPair_has_two_carrierTouchingEscapes
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7)
    {a b : Fin n} (ha : a ∈ first) (hb : b ∈ second) :
    ∃ block₁ block₂ third₁ third₂ : Finset (Fin n),
      block₁ ⊆ ambient \ (first ∪ second) ∧ block₁.card = 4 ∧
      block₂ ⊆ ambient \ (first ∪ second) ∧ block₂.card = 4 ∧
      block₁ ≠ block₂ ∧
      ¬IsStrongPolygonSet χ
        ((ambient \ (first ∪ second)) \ block₁) ∧
      ¬IsStrongPolygonSet χ
        ((ambient \ (first ∪ second)) \ block₂) ∧
      third₁ ⊆ ambient \ insert a (insert b block₁) ∧
      third₁.card = 6 ∧ IsStrongPolygonSet χ third₁ ∧
      (HasPairEscapeOccupancy first second third₁ .oneCarrier ∨
        HasPairEscapeOccupancy first second third₁ .twoCarrier) ∧
      third₂ ⊆ ambient \ insert a (insert b block₂) ∧
      third₂.card = 6 ∧ IsStrongPolygonSet χ third₂ ∧
      (HasPairEscapeOccupancy first second third₂ .oneCarrier ∨
        HasPairEscapeOccupancy first second third₂ .twoCarrier) := by
  let residual := ambient \ (first ∪ second)
  obtain ⟨block₁, block₂, hblock₁Sub, hblock₁Card,
      hblock₂Sub, hblock₂Card, hblockNe,
      hcomplement₁NotStrong, hcomplement₂NotStrong⟩ :=
    exists_two_fourBlocks_with_nonStrong_residual_complements
      (residual := residual) Finset.sdiff_subset hescape.1 hnoStrongSeven
  obtain ⟨third₁, hthird₁Sub, hthird₁Card, hthird₁Strong, hthird₁Occupancy⟩ :=
    hescape.exists_carrierTouching_witness ha hb hblock₁Sub hblock₁Card
      hcomplement₁NotStrong
  obtain ⟨third₂, hthird₂Sub, hthird₂Card, hthird₂Strong, hthird₂Occupancy⟩ :=
    hescape.exists_carrierTouching_witness ha hb hblock₂Sub hblock₂Card
      hcomplement₂NotStrong
  exact ⟨block₁, block₂, third₁, third₂,
    hblock₁Sub, hblock₁Card, hblock₂Sub, hblock₂Card, hblockNe,
    hcomplement₁NotStrong, hcomplement₂NotStrong,
    hthird₁Sub, hthird₁Card, hthird₁Strong, hthird₁Occupancy,
    hthird₂Sub, hthird₂Card, hthird₂Strong, hthird₂Occupancy⟩

end ErdosSzekeres
