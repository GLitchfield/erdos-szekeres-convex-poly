module

public import ErdosSzekeres.StructuralChargingResidualProbeReuse567

@[expose] public section

/-!
# Generic residual bad-block counting

This file separates the finite-set counting behind the state-567 probe reuse
argument from its color-specific occupancy classes.  It proves only the
multiplicative seed-cover bound needed at state 567; it does not assert a
uniform Pascal-tail theorem.
-/

namespace ErdosSzekeres

/-- Blocks whose complement in a residual set is not a strong polygon. -/
noncomputable def BadResidualBlocks {n : ℕ} (χ : TripleColoring n)
    (residual : Finset (Fin n)) (blockCard : ℕ) :
    Finset (Finset (Fin n)) := by
  classical
  exact (residual.powersetCard blockCard).filter fun block ↦
    ¬IsStrongPolygonSet χ (residual \ block)

/-- A non-strong set of cardinality `m + 1` has a non-strong predecessor of
cardinality `m`, in the range where the four-index strong-polygon law is
local to predecessor subsets. -/
theorem exists_nonStrong_pred_subset
    {n m : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (hm : 4 ≤ m)
    (hcard : support.card = m + 1)
    (hnotStrong : ¬IsStrongPolygonSet χ support) :
    ∃ pred ⊆ support,
      pred.card = m ∧ ¬IsStrongPolygonSet χ pred := by
  by_contra hnone
  apply hnotStrong
  apply isStrongPolygonSet_of_all_pred_subsets (k := m + 1) (by omega)
    hcard
  intro pred hpredSub hpredCard
  by_contra hpredNotStrong
  apply hnone
  refine ⟨pred, hpredSub, ?_, hpredNotStrong⟩
  omega

/-- If every `(W+1)`-subset of an `R = W+B` residual is non-strong, then
every `(B-1)`-seed extends to a bad `B`-block. -/
theorem badResidualBlocks_cover_seed
    {n R W B : ℕ} {χ : TripleColoring n}
    {residual seed : Finset (Fin n)}
    (hW : 4 ≤ W)
    (hB : 1 ≤ B)
    (hbalance : R = W + B)
    (hresidualCard : residual.card = R)
    (hnoStrongSucc : ¬ContainsStrongPolygonSet χ residual (W + 1))
    (hseedSub : seed ⊆ residual)
    (hseedCard : seed.card = B - 1) :
    ∃ block ∈ BadResidualBlocks χ residual B, seed ⊆ block := by
  classical
  let succ := residual \ seed
  have hsuccSub : succ ⊆ residual := Finset.sdiff_subset
  have hsuccCard : succ.card = W + 1 := by
    simp only [succ]
    rw [Finset.card_sdiff_of_subset hseedSub, hresidualCard, hseedCard,
      hbalance]
    omega
  have hsuccNotStrong : ¬IsStrongPolygonSet χ succ := by
    intro hstrong
    exact hnoStrongSucc ⟨succ, hsuccSub, hsuccCard, hstrong⟩
  obtain ⟨pred, hpredSubSucc, hpredCard, hpredNotStrong⟩ :=
    exists_nonStrong_pred_subset hW hsuccCard hsuccNotStrong
  have hpredSub : pred ⊆ residual := hpredSubSucc.trans hsuccSub
  let block := residual \ pred
  have hblockSub : block ⊆ residual := Finset.sdiff_subset
  have hblockCard : block.card = B := by
    simp only [block]
    rw [Finset.card_sdiff_of_subset hpredSub, hresidualCard, hpredCard,
      hbalance]
    omega
  have hseedBlock : seed ⊆ block := by
    intro x hxSeed
    apply Finset.mem_sdiff.mpr
    refine ⟨hseedSub hxSeed, ?_⟩
    intro hxPred
    exact (Finset.mem_sdiff.mp (hpredSubSucc hxPred)).2 hxSeed
  refine ⟨block, ?_, hseedBlock⟩
  change block ∈ (residual.powersetCard B).filter
    (fun candidate ↦ ¬IsStrongPolygonSet χ (residual \ candidate))
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨hblockSub, hblockCard⟩, ?_⟩
  simpa only [block, Finset.sdiff_sdiff_eq_self hpredSub] using
    hpredNotStrong

/-- A family of `B`-blocks covering all `(B-1)`-seeds has the division-free
lower bound `choose R (B-1) ≤ family.card * B`. -/
theorem choose_le_badResidualBlocks_card_mul
    {n R B : ℕ} {χ : TripleColoring n}
    {residual : Finset (Fin n)}
    (hB : 1 ≤ B)
    (hresidualCard : residual.card = R)
    (hseedCover : ∀ seed ∈ residual.powersetCard (B - 1),
      ∃ block ∈ BadResidualBlocks χ residual B, seed ⊆ block) :
    Nat.choose R (B - 1) ≤
      (BadResidualBlocks χ residual B).card * B := by
  classical
  have hcover :
      residual.powersetCard (B - 1) ⊆
        (BadResidualBlocks χ residual B).biUnion
          (fun block ↦ block.powersetCard (B - 1)) := by
    intro seed hseed
    obtain ⟨block, hblock, hseedBlock⟩ := hseedCover seed hseed
    apply Finset.mem_biUnion.mpr
    refine ⟨block, hblock, ?_⟩
    exact Finset.mem_powersetCard.mpr
      ⟨hseedBlock, (Finset.mem_powersetCard.mp hseed).2⟩
  calc
    Nat.choose R (B - 1) = (residual.powersetCard (B - 1)).card := by
      rw [Finset.card_powersetCard, hresidualCard]
    _ ≤ ((BadResidualBlocks χ residual B).biUnion
        (fun block ↦ block.powersetCard (B - 1))).card :=
      Finset.card_le_card hcover
    _ ≤ (BadResidualBlocks χ residual B).card * B := by
      apply Finset.card_biUnion_le_card_mul
      intro block hblock
      change block ∈ (residual.powersetCard B).filter
        (fun candidate ↦ ¬IsStrongPolygonSet χ (residual \ candidate)) at hblock
      have hblockCard :=
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hblock).1).2
      rw [Finset.card_powersetCard, hblockCard]
      calc
        Nat.choose B (B - 1) = Nat.choose B 1 := by
          exact Nat.choose_symm hB
        _ = B := Nat.choose_one_right B
        _ ≤ B := le_rfl

/-- Seed coverage, a cover by witness fibers, and a bound on the number of
same-class-distinct-free witnesses force either a class collision or a fiber
strictly larger than `M`. -/
theorem badResidualBlocks_collision_or_largeFiber
    {n R B C M : ℕ} {χ : TripleColoring n}
    {residual : Finset (Fin n)}
    {ι : Type*} [DecidableEq ι]
    (witnesses : Finset ι)
    (fiber : ι → Finset (Finset (Fin n)))
    (sameClass : ι → ι → Prop)
    (hB : 1 ≤ B)
    (hresidualCard : residual.card = R)
    (hseedCover : ∀ seed ∈ residual.powersetCard (B - 1),
      ∃ block ∈ BadResidualBlocks χ residual B, seed ⊆ block)
    (hprobeCover : BadResidualBlocks χ residual B ⊆
      witnesses.biUnion fiber)
    (hclassBound :
      (¬∃ w₁ ∈ witnesses, ∃ w₂ ∈ witnesses,
          w₁ ≠ w₂ ∧ sameClass w₁ w₂) →
        witnesses.card ≤ C)
    (hgap : (C * M) * B < Nat.choose R (B - 1)) :
    (∃ w₁ ∈ witnesses, ∃ w₂ ∈ witnesses,
      w₁ ≠ w₂ ∧ sameClass w₁ w₂) ∨
    ∃ w ∈ witnesses, M < (fiber w).card := by
  classical
  by_cases hcollision :
      ∃ w₁ ∈ witnesses, ∃ w₂ ∈ witnesses,
        w₁ ≠ w₂ ∧ sameClass w₁ w₂
  · exact Or.inl hcollision
  · right
    by_contra hnoLarge
    push Not at hnoLarge
    have hwitnessesCard : witnesses.card ≤ C := hclassBound hcollision
    have hunionCard : (witnesses.biUnion fiber).card ≤ witnesses.card * M := by
      apply Finset.card_biUnion_le_card_mul
      intro w hw
      exact hnoLarge w hw
    have hbadCard : (BadResidualBlocks χ residual B).card ≤ C * M := by
      exact (Finset.card_le_card hprobeCover).trans
        (hunionCard.trans (Nat.mul_le_mul_right M hwitnessesCard))
    have hcount := choose_le_badResidualBlocks_card_mul hB hresidualCard
      hseedCover
    have hupper :
        (BadResidualBlocks χ residual B).card * B ≤ (C * M) * B :=
      Nat.mul_le_mul_right B hbadCard
    omega

/-- The generic multiplicative count specializes at
`(R,W,B,C,M) = (10,6,4,2,14)` to the existing state-567 disjunction. -/
theorem exists_sameOccupancyCollision_or_fifteenProbeWitness567_via_generic
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7)
    {a b : Fin n} (ha : a ∈ first) (hb : b ∈ second) :
    (∃ third₁ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
      ∃ third₂ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
        third₁ ≠ third₂ ∧
          SameCarrierTouchingOccupancy567 first second third₁ third₂) ∨
    ∃ third ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
      15 ≤ (CarrierTouchingProbeFiber567 χ ambient first second a b third).card := by
  classical
  let residual := ambient \ (first ∪ second)
  let witnesses := CarrierTouchingProbeWitnesses567 χ ambient first second a b
  let fiber := fun third ↦
    CarrierTouchingProbeFiber567 χ ambient first second a b third
  let sameClass := SameCarrierTouchingOccupancy567 first second
  have hnoStrongResidual : ¬ContainsStrongPolygonSet χ residual 7 := by
    intro hstrong
    exact hnoStrongSeven
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.sdiff_subset)
  have hseedCover : ∀ seed ∈ residual.powersetCard (4 - 1),
      ∃ block ∈ BadResidualBlocks χ residual 4, seed ⊆ block := by
    intro seed hseed
    have hseedData := Finset.mem_powersetCard.mp hseed
    exact badResidualBlocks_cover_seed
      (R := 10) (W := 6) (B := 4)
      (by norm_num) (by norm_num) (by norm_num) hescape.1
      hnoStrongResidual hseedData.1 hseedData.2
  have hprobeCover : BadResidualBlocks χ residual 4 ⊆
      witnesses.biUnion fiber := by
    intro block hblock
    obtain ⟨third, hincident⟩ :=
      hescape.badProbe_has_incident_witness ha hb (by
        simpa [BadResidualBlocks, BadResidualFourBlocks567, residual] using hblock)
    apply Finset.mem_biUnion.mpr
    refine ⟨third, ?_, ?_⟩
    · change third ∈ (ambient.powersetCard 6).filter
        (fun candidate ↦ ∃ probe,
          IsCarrierTouchingProbeWitness567 χ ambient first second
            a b probe candidate)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr
          ⟨hincident.2.1.trans Finset.sdiff_subset, hincident.2.2.1⟩,
          block, hincident⟩
    · change block ∈
        (BadResidualFourBlocks567 χ residual).filter
          (fun candidate ↦ IsCarrierTouchingProbeWitness567 χ ambient
            first second a b candidate third)
      exact Finset.mem_filter.mpr
        ⟨by simpa [BadResidualBlocks, BadResidualFourBlocks567] using hblock,
          hincident⟩
  have hclassBound :
      (¬∃ third₁ ∈ witnesses, ∃ third₂ ∈ witnesses,
          third₁ ≠ third₂ ∧ sameClass third₁ third₂) →
        witnesses.card ≤ 2 := by
    intro hcollision
    have hnoCollision :
        ∀ third₁ ∈ witnesses, ∀ third₂ ∈ witnesses,
          sameClass third₁ third₂ → third₁ = third₂ := by
      intro third₁ hthird₁ third₂ hthird₂ hsame
      by_contra hne
      exact hcollision ⟨third₁, hthird₁, third₂, hthird₂, hne, hsame⟩
    let oneWitnesses := witnesses.filter fun third ↦
      HasPairEscapeOccupancy first second third .oneCarrier
    let twoWitnesses := witnesses.filter fun third ↦
      HasPairEscapeOccupancy first second third .twoCarrier
    have hwitnessesSub : witnesses ⊆ oneWitnesses ∪ twoWitnesses := by
      intro third hthird
      have hthirdWitnesses : third ∈ witnesses := hthird
      change third ∈ (ambient.powersetCard 6).filter
        (fun candidate ↦ ∃ block,
          IsCarrierTouchingProbeWitness567 χ ambient first second
            a b block candidate) at hthird
      obtain ⟨block, hincident⟩ := (Finset.mem_filter.mp hthird).2
      rcases hincident.2.2.2.2 with hone | htwo
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hthirdWitnesses, hone⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hthirdWitnesses, htwo⟩)
    have honeCard : oneWitnesses.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro third₁ hthird₁ third₂ hthird₂
      have hdata₁ := Finset.mem_filter.mp hthird₁
      have hdata₂ := Finset.mem_filter.mp hthird₂
      exact hnoCollision third₁ hdata₁.1 third₂ hdata₂.1
        (Or.inl ⟨hdata₁.2, hdata₂.2⟩)
    have htwoCard : twoWitnesses.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro third₁ hthird₁ third₂ hthird₂
      have hdata₁ := Finset.mem_filter.mp hthird₁
      have hdata₂ := Finset.mem_filter.mp hthird₂
      exact hnoCollision third₁ hdata₁.1 third₂ hdata₂.1
        (Or.inr ⟨hdata₁.2, hdata₂.2⟩)
    have hunion := Finset.card_union_le oneWitnesses twoWitnesses
    exact (Finset.card_le_card hwitnessesSub).trans (by omega)
  have hgeneric := badResidualBlocks_collision_or_largeFiber
    (R := 10) (B := 4) (C := 2) (M := 14)
    (χ := χ) (residual := residual)
    witnesses fiber sameClass (by norm_num) hescape.1 hseedCover
    hprobeCover hclassBound (by norm_num [Nat.choose])
  rcases hgeneric with hcollision | ⟨third, hthird, hhigh⟩
  · exact Or.inl (by simpa [witnesses, sameClass] using hcollision)
  · right
    refine ⟨third, by simpa [witnesses] using hthird, ?_⟩
    have : 14 <
        (CarrierTouchingProbeFiber567 χ ambient first second a b third).card := by
      simpa [fiber] using hhigh
    omega

end ErdosSzekeres

end
