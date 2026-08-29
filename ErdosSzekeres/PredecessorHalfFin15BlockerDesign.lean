module

public import ErdosSzekeres.PredecessorHalfFin15Obstruction

@[expose] public section

/-!
# The seven-point blocker design

Four-point blockers in a seven-point support have three-point complements.
When distinct blockers meet in at most two points, the pairs contained in
their complements are disjoint.  This gives the sharp seven-block bound and
the Steiner incidence structure in the equality case.
-/

namespace ErdosSzekeres

/-- A two-point set contained in the complements of two four-point blocks
determines the block when distinct blocks meet in at most two points. -/
theorem fourBlock_eq_of_common_complement_pair
    {α : Type*} [DecidableEq α]
    (support block₁ block₂ pair : Finset α)
    (hsupport : support.card = 7)
    (hblock₁Sub : block₁ ⊆ support) (hblock₂Sub : block₂ ⊆ support)
    (hblock₁Card : block₁.card = 4) (hblock₂Card : block₂.card = 4)
    (hsmallInter : block₁ ≠ block₂ → (block₁ ∩ block₂).card ≤ 2)
    (hpair₁ : pair ∈ (support \ block₁).powersetCard 2)
    (hpair₂ : pair ∈ (support \ block₂).powersetCard 2) :
    block₁ = block₂ := by
  by_contra hblocksNe
  have hpair₁Data := Finset.mem_powersetCard.mp hpair₁
  have hpair₂Data := Finset.mem_powersetCard.mp hpair₂
  have hpairSub : pair ⊆ (support \ block₁) ∩ (support \ block₂) := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hpair₁Data.1 hx, hpair₂Data.1 hx⟩
  have hcomplementInter :
      2 ≤ ((support \ block₁) ∩ (support \ block₂)).card := by
    rw [← hpair₁Data.2]
    exact Finset.card_le_card hpairSub
  rw [← Finset.sdiff_union_distrib] at hcomplementInter
  have hunionSub : block₁ ∪ block₂ ⊆ support :=
    Finset.union_subset hblock₁Sub hblock₂Sub
  have hcomplementCard :
      (support \ (block₁ ∪ block₂)).card = 7 - (block₁ ∪ block₂).card := by
    rw [Finset.card_sdiff_of_subset hunionSub, hsupport]
  have hunionInter := Finset.card_union_add_card_inter block₁ block₂
  have hsmall := hsmallInter hblocksNe
  omega

/-- Eight selected four-point blocks on a seven-point support either have
high multiplicity, or their distinct complements form the unique-pair
incidence design at the extremal size. -/
theorem eight_fourBlock_family_fano_classification
    {α : Type*} [DecidableEq α]
    (support : Finset α) (anchor : Fin 8 → Finset α)
    (hsupport : support.card = 7)
    (hanchorSub : ∀ i, anchor i ⊆ support)
    (hanchorCard : ∀ i, (anchor i).card = 4)
    (hsmallInter : ∀ i j, anchor i ≠ anchor j →
      ((anchor i) ∩ (anchor j)).card ≤ 2) :
    let blocks := Finset.univ.image anchor
    blocks.card ≤ 7 ∧
      (blocks.card = 7 →
        ∀ pair : Finset α, pair ⊆ support → pair.card = 2 →
          ∃! block : Finset α, block ∈ blocks ∧ pair ⊆ support \ block) ∧
      (blocks.card ≤ 6 →
        (∃ block ∈ blocks,
          3 ≤ (Finset.univ.filter fun i : Fin 8 ↦ anchor i = block).card) ∨
        ∃ block₁ ∈ blocks, ∃ block₂ ∈ blocks, block₁ ≠ block₂ ∧
          2 ≤ (Finset.univ.filter fun i : Fin 8 ↦ anchor i = block₁).card ∧
          2 ≤ (Finset.univ.filter fun i : Fin 8 ↦ anchor i = block₂).card) := by
  classical
  let blocks : Finset (Finset α) := Finset.univ.image anchor
  let pairFamily : Finset α → Finset (Finset α) := fun block ↦
    (support \ block).powersetCard 2
  let pairUnion : Finset (Finset α) := blocks.biUnion pairFamily
  change blocks.card ≤ 7 ∧
    (blocks.card = 7 →
      ∀ pair : Finset α, pair ⊆ support → pair.card = 2 →
        ∃! block : Finset α, block ∈ blocks ∧ pair ⊆ support \ block) ∧
    (blocks.card ≤ 6 →
      (∃ block ∈ blocks,
        3 ≤ (Finset.univ.filter fun i : Fin 8 ↦ anchor i = block).card) ∨
      ∃ block₁ ∈ blocks, ∃ block₂ ∈ blocks, block₁ ≠ block₂ ∧
        2 ≤ (Finset.univ.filter fun i : Fin 8 ↦ anchor i = block₁).card ∧
        2 ≤ (Finset.univ.filter fun i : Fin 8 ↦ anchor i = block₂).card)
  have hblockData {block : Finset α} (hblock : block ∈ blocks) :
      block ⊆ support ∧ block.card = 4 ∧ ∃ i : Fin 8, anchor i = block := by
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hblock
    exact ⟨hanchorSub i, hanchorCard i, i, rfl⟩
  have hcomplementCard {block : Finset α} (hblock : block ∈ blocks) :
      (support \ block).card = 3 := by
    rw [Finset.card_sdiff_of_subset (hblockData hblock).1,
      hsupport, (hblockData hblock).2.1]
  have hblockEq {block₁ block₂ pair : Finset α}
      (hblock₁ : block₁ ∈ blocks) (hblock₂ : block₂ ∈ blocks)
      (hpair₁ : pair ∈ pairFamily block₁)
      (hpair₂ : pair ∈ pairFamily block₂) :
      block₁ = block₂ := by
    obtain ⟨i, hi⟩ := (hblockData hblock₁).2.2
    obtain ⟨j, hj⟩ := (hblockData hblock₂).2.2
    apply fourBlock_eq_of_common_complement_pair support block₁ block₂ pair
      hsupport (hblockData hblock₁).1 (hblockData hblock₂).1
      (hblockData hblock₁).2.1 (hblockData hblock₂).2.1
    · intro hblocksNe
      have hanchorsNe : anchor i ≠ anchor j := by
        intro hanchorsEq
        apply hblocksNe
        exact hi.symm.trans (hanchorsEq.trans hj)
      simpa [hi, hj] using hsmallInter i j hanchorsNe
    · simpa [pairFamily] using hpair₁
    · simpa [pairFamily] using hpair₂
  have hpairwise :
      (blocks : Set (Finset α)).PairwiseDisjoint pairFamily := by
    intro block₁ hblock₁ block₂ hblock₂ hblocksNe
    apply Finset.disjoint_left.mpr
    intro pair hpair₁ hpair₂
    exact hblocksNe (hblockEq hblock₁ hblock₂ hpair₁ hpair₂)
  have hpairUnionSub : pairUnion ⊆ support.powersetCard 2 := by
    intro pair hpair
    change pair ∈ blocks.biUnion pairFamily at hpair
    obtain ⟨block, hblock, hpairBlock⟩ := Finset.mem_biUnion.mp hpair
    have hpairData := Finset.mem_powersetCard.mp
      (show pair ∈ (support \ block).powersetCard 2 by
        simpa [pairFamily] using hpairBlock)
    exact Finset.mem_powersetCard.mpr
      ⟨hpairData.1.trans Finset.sdiff_subset, hpairData.2⟩
  have hpairUnionCard : pairUnion.card = blocks.card * 3 := by
    calc
      pairUnion.card = ∑ block ∈ blocks, (pairFamily block).card := by
        simpa [pairUnion] using Finset.card_biUnion hpairwise
      _ = blocks.card * 3 := by
        apply Finset.sum_const_nat
        intro block hblock
        simp [pairFamily, hcomplementCard hblock]
  have hsupportPairCard : (support.powersetCard 2).card = 21 := by
    simp [hsupport, Nat.choose]
  have hblocksLeSeven : blocks.card ≤ 7 := by
    have hcardLe := Finset.card_le_card hpairUnionSub
    rw [hpairUnionCard, hsupportPairCard] at hcardLe
    omega
  have hfano : blocks.card = 7 →
      ∀ pair : Finset α, pair ⊆ support → pair.card = 2 →
        ∃! block : Finset α, block ∈ blocks ∧ pair ⊆ support \ block := by
    intro hblocksCard pair hpairSub hpairCard
    have hpairUnionEq : pairUnion = support.powersetCard 2 := by
      apply Finset.eq_of_subset_of_card_le hpairUnionSub
      rw [hpairUnionCard, hsupportPairCard, hblocksCard]
    have hpairMem : pair ∈ pairUnion := by
      rw [hpairUnionEq]
      exact Finset.mem_powersetCard.mpr ⟨hpairSub, hpairCard⟩
    change pair ∈ blocks.biUnion pairFamily at hpairMem
    obtain ⟨block, hblock, hpairBlock⟩ := Finset.mem_biUnion.mp hpairMem
    have hpairBlockData := Finset.mem_powersetCard.mp
      (show pair ∈ (support \ block).powersetCard 2 by
        simpa [pairFamily] using hpairBlock)
    refine ⟨block, ⟨hblock, hpairBlockData.1⟩, ?_⟩
    intro other hother
    have hpairOther : pair ∈ (support \ other).powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨hother.2, hpairCard⟩
    have hblocksEq := hblockEq hblock hother.1 hpairBlock
      (show pair ∈ pairFamily other by
        simpa [pairFamily] using hpairOther)
    exact hblocksEq.symm
  let fiber : Finset α → Finset (Fin 8) := fun block ↦
    Finset.univ.filter fun i : Fin 8 ↦ anchor i = block
  have hsumFibers : (∑ block ∈ blocks, (fiber block).card) = 8 := by
    calc
      (∑ block ∈ blocks, (fiber block).card) =
          (Finset.univ.filter fun i : Fin 8 ↦ anchor i ∈ blocks).card := by
        simpa [fiber] using
          (Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset (Fin 8)) blocks anchor)
      _ = 8 := by simp [blocks]
  have hmultiplicity : blocks.card ≤ 6 →
      (∃ block ∈ blocks, 3 ≤ (fiber block).card) ∨
      ∃ block₁ ∈ blocks, ∃ block₂ ∈ blocks, block₁ ≠ block₂ ∧
        2 ≤ (fiber block₁).card ∧ 2 ≤ (fiber block₂).card := by
    intro hblocksSix
    by_cases hthree : ∃ block ∈ blocks, 3 ≤ (fiber block).card
    · exact Or.inl hthree
    · apply Or.inr
      have hfiberLeTwo : ∀ block ∈ blocks, (fiber block).card ≤ 2 := by
        intro block hblock
        by_contra hlarge
        apply hthree
        exact ⟨block, hblock, by omega⟩
      have hduplicate : ∃ block ∈ blocks, 2 ≤ (fiber block).card := by
        by_contra hnone
        have hfiberLeOne : ∀ block ∈ blocks, (fiber block).card ≤ 1 := by
          intro block hblock
          by_contra hlarge
          apply hnone
          exact ⟨block, hblock, by omega⟩
        have hsumLe :
            (∑ block ∈ blocks, (fiber block).card) ≤ blocks.card * 1 :=
          Finset.sum_le_card_nsmul blocks (fun block ↦ (fiber block).card) 1
            hfiberLeOne
        rw [hsumFibers] at hsumLe
        omega
      obtain ⟨block₁, hblock₁, hblock₁Degree⟩ := hduplicate
      refine ⟨block₁, hblock₁, ?_⟩
      by_contra hsecond
      have hotherLeOne : ∀ block ∈ blocks.erase block₁,
          (fiber block).card ≤ 1 := by
        intro block hblock
        have hblockData := Finset.mem_erase.mp hblock
        by_contra hlarge
        apply hsecond
        exact ⟨block, hblockData.2, hblockData.1.symm,
          hblock₁Degree, by omega⟩
      have hotherSumLe :
          (∑ block ∈ blocks.erase block₁, (fiber block).card) ≤
            (blocks.erase block₁).card * 1 :=
        Finset.sum_le_card_nsmul (blocks.erase block₁)
          (fun block ↦ (fiber block).card) 1 hotherLeOne
      have hsplit :
          (fiber block₁).card +
              (∑ block ∈ blocks.erase block₁, (fiber block).card) =
            ∑ block ∈ blocks, (fiber block).card := by
        exact Finset.add_sum_erase blocks
          (fun block ↦ (fiber block).card) hblock₁
      have hblock₁Le := hfiberLeTwo block₁ hblock₁
      have heraseCard := Finset.card_erase_of_mem hblock₁
      have hotherSumLe' :
          (∑ block ∈ blocks.erase block₁, (fiber block).card) ≤
            (blocks.erase block₁).card := by
        simpa using hotherSumLe
      have htotalLe :
          (∑ block ∈ blocks, (fiber block).card) ≤
            2 + (blocks.erase block₁).card := by
        calc
          (∑ block ∈ blocks, (fiber block).card) =
              (fiber block₁).card +
                ∑ block ∈ blocks.erase block₁, (fiber block).card := hsplit.symm
          _ ≤ 2 + (blocks.erase block₁).card :=
            Nat.add_le_add hblock₁Le hotherSumLe'
      omega
  exact ⟨hblocksLeSeven, hfano, hmultiplicity⟩

end ErdosSzekeres

end
