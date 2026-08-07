module

public import ErdosSzekeres.StructuralChargingTransitionHallUncrossing

@[expose] public section

/-!
# One-hole descent as a sufficient condition for block expansion

Pairwise meet/join closure does not itself produce distinct representatives.
This file isolates the stronger mechanism needed by a local augmentation
proof.  A one-hole state represents every span in a finite block except one;
if the hole has an unused candidate, the state completes immediately.  More
generally, a strict descent from every unfillable state must terminate at a
fillable state and therefore yields a system of distinct representatives.

The descent theorem is independent of any proposed geometric measure.  It
accepts an arbitrary well-founded relation, so a later proof may use a
lexicographic or other structural measure without encoding it into a natural
number.
-/

namespace ErdosSzekeres

/-- A partial system of distinct representatives with exactly one designated
span omitted.  Values outside `block.erase hole` are irrelevant. -/
structure FiniteCandidateHoleState
    {Span Ideal : Type*} [DecidableEq Span]
    (block : Finset Span) (candidates : Span → Finset Ideal) where
  hole : Span
  hole_mem : hole ∈ block
  representative : Span → Ideal
  representative_mem : ∀ span ∈ block.erase hole,
    representative span ∈ candidates span
  representative_injective :
    Set.InjOn representative (block.erase hole)

/-- The hole can be filled when one of its candidates is unused by every
currently represented span. -/
def FiniteCandidateHoleState.CanFill
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates) : Prop :=
  ∃ ideal ∈ candidates state.hole,
    ∀ span ∈ block.erase state.hole,
      ideal ≠ state.representative span

/-- A two-step augmenting exit first transfers an occupied candidate to the
hole, then fills the displaced owner's hole with an ideal unused by the
original partial representative system. -/
def FiniteCandidateHoleState.HasTwoStepAugmentingExit
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates) : Prop :=
  ∃ ideal ∈ candidates state.hole,
    ∃ owner ∈ block.erase state.hole,
      state.representative owner = ideal ∧
        ∃ fresh ∈ candidates owner,
          ∀ span ∈ block.erase state.hole,
            fresh ≠ state.representative span

/-- A closed saturated owner-star is the exact local obstruction to both a
direct fill and a two-step augmentation.  Every hole candidate is currently
owned, and every candidate of every reachable owner is currently used. -/
def FiniteCandidateHoleState.HasClosedSaturatedOwnerStar
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates) : Prop :=
  (∀ ideal ∈ candidates state.hole,
      ∃ owner ∈ block.erase state.hole,
        state.representative owner = ideal) ∧
    ∀ ideal ∈ candidates state.hole,
      ∀ owner ∈ block.erase state.hole,
        state.representative owner = ideal →
          ∀ fresh ∈ candidates owner,
            ∃ span ∈ block.erase state.hole,
              state.representative span = fresh

/-- The spans whose current representatives belong to the hole's candidate
family.  In a blocked state these are precisely the unique current owners of
the hole candidates. -/
def FiniteCandidateHoleState.reachedOwners
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates) : Finset Span :=
  (block.erase state.hole).filter fun owner ↦
    state.representative owner ∈ candidates state.hole

/-- The hole family together with every candidate family reached through an
actual current owner. -/
def FiniteCandidateHoleState.ownerStar
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates) : Finset Ideal :=
  candidates state.hole ∪ state.reachedOwners.biUnion candidates

/-- Every injective membership-feasible assignment of a hole family's ideals
to distinct non-hole spans has a block-large owner star.  This profile depends
only on the candidate system, not on a partial representative state. -/
def FiniteCandidateFeasibleOwnerStarExpansion
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    (block : Finset Span) (candidates : Span → Finset Ideal) : Prop :=
  ∀ hole ∈ block, ∀ owner : Ideal → Span,
    Set.InjOn owner (candidates hole) →
      (∀ ideal ∈ candidates hole,
        owner ideal ∈ block.erase hole ∧
          ideal ∈ candidates (owner ideal)) →
        block.card ≤
          (candidates hole ∪
            ((candidates hole).image owner).biUnion candidates).card

/-- Every feasible owner map reaches at least one individual owner family as
large as the block.  This is a stronger, state-free sufficient profile for
owner-star expansion. -/
def FiniteCandidateFeasibleOwnerHasBlockLargeFamily
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    (block : Finset Span) (candidates : Span → Finset Ideal) : Prop :=
  ∀ hole ∈ block, ∀ owner : Ideal → Span,
    Set.InjOn owner (candidates hole) →
      (∀ ideal ∈ candidates hole,
        owner ideal ∈ block.erase hole ∧
          ideal ∈ candidates (owner ideal)) →
        ∃ ideal ∈ candidates hole,
          block.card ≤ (candidates (owner ideal)).card

/-- A block-large mapped owner is contained in the corresponding owner star,
so the stronger feasible-owner profile implies feasible-owner-star expansion. -/
theorem finiteCandidateFeasibleOwnerStarExpansion_of_blockLargeFamily
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (hprofile :
      FiniteCandidateFeasibleOwnerHasBlockLargeFamily block candidates) :
    FiniteCandidateFeasibleOwnerStarExpansion block candidates := by
  intro hole hhole owner hinjective hfeasible
  obtain ⟨ideal, hideal, hlarge⟩ :=
    hprofile hole hhole owner hinjective hfeasible
  apply hlarge.trans
  apply Finset.card_le_card
  intro candidate hcandidate
  rw [Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨owner ideal, Finset.mem_image.mpr ⟨ideal, hideal, rfl⟩,
    hcandidate⟩

/-- The positive closed-star predicate exactly characterizes simultaneous
failure of the direct and length-two exits. -/
theorem FiniteCandidateHoleState.hasClosedSaturatedOwnerStar_iff
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates) :
    state.HasClosedSaturatedOwnerStar ↔
      ¬ state.CanFill ∧ ¬ state.HasTwoStepAugmentingExit := by
  constructor
  · rintro ⟨howned, hsaturated⟩
    constructor
    · rintro ⟨ideal, hideal, hunused⟩
      obtain ⟨owner, howner, hvalue⟩ := howned ideal hideal
      exact hunused owner howner hvalue.symm
    · rintro ⟨ideal, hideal, owner, howner, hvalue,
        fresh, hfresh, hunused⟩
      obtain ⟨span, hspan, hspanvalue⟩ :=
        hsaturated ideal hideal owner howner hvalue fresh hfresh
      exact hunused span hspan hspanvalue.symm
  · rintro ⟨hnotFill, hnotExit⟩
    constructor
    · intro ideal hideal
      by_contra hnone
      apply hnotFill
      refine ⟨ideal, hideal, ?_⟩
      intro owner howner heq
      apply hnone
      exact ⟨owner, howner, heq.symm⟩
    · intro ideal hideal owner howner hvalue fresh hfresh
      by_contra hnone
      apply hnotExit
      refine ⟨ideal, hideal, owner, howner, hvalue, fresh, hfresh, ?_⟩
      intro span hspan heq
      apply hnone
      exact ⟨span, hspan, heq.symm⟩

/-- Excluding a closed saturated owner-star is exactly enough to obtain one of
the two constructive exits. -/
theorem FiniteCandidateHoleState.canFill_or_hasTwoStepAugmentingExit_of_not_closedStar
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hnotClosed : ¬ state.HasClosedSaturatedOwnerStar) :
    state.CanFill ∨ state.HasTwoStepAugmentingExit := by
  by_cases hfill : state.CanFill
  · exact Or.inl hfill
  · right
    by_contra hexit
    exact hnotClosed
      (state.hasClosedSaturatedOwnerStar_iff.mpr ⟨hfill, hexit⟩)

/-- Expansion of the canonical current-owner star forces a two-step exit from
any blocked state.  This is a state-dependent local inequality, not a Hall
premise on arbitrary span subfamilies. -/
theorem FiniteCandidateHoleState.hasTwoStepAugmentingExit_of_ownerStarExpansion
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hblocked : ¬ state.CanFill)
    (hexpand : block.card ≤ state.ownerStar.card) :
    state.HasTwoStepAugmentingExit := by
  have hnotClosed : ¬ state.HasClosedSaturatedOwnerStar := by
    intro hclosed
    let used := (block.erase state.hole).image state.representative
    have hstarSubset : state.ownerStar ⊆ used := by
      intro ideal hideal
      rw [FiniteCandidateHoleState.ownerStar, Finset.mem_union] at hideal
      rcases hideal with hideal | hideal
      · obtain ⟨owner, howner, hvalue⟩ := hclosed.1 ideal hideal
        rw [Finset.mem_image]
        exact ⟨owner, howner, hvalue⟩
      · rw [Finset.mem_biUnion] at hideal
        obtain ⟨owner, howner, hidealOwner⟩ := hideal
        rw [FiniteCandidateHoleState.reachedOwners,
          Finset.mem_filter] at howner
        obtain ⟨span, hspan, hvalue⟩ := hclosed.2
          (state.representative owner) howner.2 owner howner.1 rfl
          ideal hidealOwner
        rw [Finset.mem_image]
        exact ⟨span, hspan, hvalue⟩
    have hstarCard : state.ownerStar.card ≤ used.card :=
      Finset.card_le_card hstarSubset
    have husedCard : used.card = (block.erase state.hole).card :=
      Finset.card_image_iff.mpr state.representative_injective
    rw [husedCard, Finset.card_erase_of_mem state.hole_mem] at hstarCard
    have hblockPositive : 0 < block.card :=
      Finset.card_pos.mpr ⟨state.hole, state.hole_mem⟩
    omega
  exact (state.canFill_or_hasTwoStepAugmentingExit_of_not_closedStar
    hnotClosed).resolve_left hblocked

/-- A blocked state turns its uniquely represented hole candidates into one
of the feasible owner maps quantified by the state-free expansion profile. -/
theorem FiniteCandidateHoleState.ownerStarExpansion_of_feasibleOwnerStarExpansion
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hprofile : FiniteCandidateFeasibleOwnerStarExpansion block candidates)
    (hblocked : ¬ state.CanFill) :
    block.card ≤ state.ownerStar.card := by
  classical
  have howned : ∀ ideal ∈ candidates state.hole,
      ∃ owner ∈ block.erase state.hole,
        state.representative owner = ideal := by
    intro ideal hideal
    by_contra hnone
    apply hblocked
    refine ⟨ideal, hideal, ?_⟩
    intro owner howner heq
    apply hnone
    exact ⟨owner, howner, heq.symm⟩
  let owner : Ideal → Span := fun ideal ↦
    if hideal : ideal ∈ candidates state.hole then
      Classical.choose (howned ideal hideal)
    else state.hole
  have hownerSpec (ideal : Ideal) (hideal : ideal ∈ candidates state.hole) :
      owner ideal ∈ block.erase state.hole ∧
        state.representative (owner ideal) = ideal := by
    simp only [owner, dif_pos hideal]
    exact Classical.choose_spec (howned ideal hideal)
  have hownerInjective : Set.InjOn owner (candidates state.hole) := by
    intro first hfirst second hsecond heq
    have hfirstSpec := hownerSpec first hfirst
    have hsecondSpec := hownerSpec second hsecond
    calc
      first = state.representative (owner first) := hfirstSpec.2.symm
      _ = state.representative (owner second) := congrArg state.representative heq
      _ = second := hsecondSpec.2
  have hownerFeasible : ∀ ideal ∈ candidates state.hole,
      owner ideal ∈ block.erase state.hole ∧
        ideal ∈ candidates (owner ideal) := by
    intro ideal hideal
    have hspec := hownerSpec ideal hideal
    refine ⟨hspec.1, ?_⟩
    simpa [hspec.2] using
      state.representative_mem (owner ideal) hspec.1
  have hmappedExpansion := hprofile state.hole state.hole_mem owner
    hownerInjective hownerFeasible
  apply hmappedExpansion.trans
  apply Finset.card_le_card
  intro ideal hideal
  rw [FiniteCandidateHoleState.ownerStar, Finset.mem_union]
  rw [Finset.mem_union] at hideal
  rcases hideal with hideal | hideal
  · exact Or.inl hideal
  · right
    rw [Finset.mem_biUnion] at hideal ⊢
    obtain ⟨ownerSpan, hownerSpan, hidealOwner⟩ := hideal
    rw [Finset.mem_image] at hownerSpan
    obtain ⟨source, hsource, rfl⟩ := hownerSpan
    have hspec := hownerSpec source hsource
    refine ⟨owner source, ?_, hidealOwner⟩
    rw [FiniteCandidateHoleState.reachedOwners, Finset.mem_filter]
    exact ⟨hspec.1, by simpa [hspec.2] using hsource⟩

/-- The state-free feasible-owner profile therefore forces the exact two-step
exit from every blocked one-hole state. -/
theorem FiniteCandidateHoleState.hasTwoStepAugmentingExit_of_feasibleOwnerStarExpansion
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hprofile : FiniteCandidateFeasibleOwnerStarExpansion block candidates)
    (hblocked : ¬ state.CanFill) :
    state.HasTwoStepAugmentingExit := by
  exact state.hasTwoStepAugmentingExit_of_ownerStarExpansion hblocked
    (state.ownerStarExpansion_of_feasibleOwnerStarExpansion
      hprofile hblocked)

/-- A system of distinct representatives restricted to one finite block. -/
def FiniteCandidateHasDistinctRepresentativesOn
    {Span Ideal : Type*} (block : Finset Span)
    (candidates : Span → Finset Ideal) : Prop :=
  ∃ representative : Span → Ideal,
    Set.InjOn representative block ∧
      ∀ span ∈ block, representative span ∈ candidates span

/-- Every candidate family in the block is a singleton or has at least as
many members as the block. -/
def SingletonOrBlockLarge
    {Span Ideal : Type*} [DecidableEq Ideal]
    (block : Finset Span) (candidates : Span → Finset Ideal) : Prop :=
  ∀ span ∈ block,
    (candidates span).card = 1 ∨
      block.card ≤ (candidates span).card

/-- Any other block member that can own the ideal of a singleton candidate
family has a candidate family at least as large as the block. -/
def SingletonCandidateOwnersBlockLarge
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    (block : Finset Span) (candidates : Span → Finset Ideal) : Prop :=
  ∀ singleton ∈ block, ∀ ideal,
    candidates singleton = {ideal} →
      ∀ owner ∈ block.erase singleton,
        ideal ∈ candidates owner →
          block.card ≤ (candidates owner).card

/-- More candidates for the hole than occupied representatives force an
unused candidate.  This is the elementary cardinality exit from a descent. -/
theorem FiniteCandidateHoleState.canFill_of_erase_card_lt_candidates_card
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hcard : (block.erase state.hole).card <
      (candidates state.hole).card) :
    state.CanFill := by
  let used := (block.erase state.hole).image state.representative
  have husedCard : used.card ≤ (block.erase state.hole).card := by
    exact Finset.card_image_le
  have hnotSubset : ¬ candidates state.hole ⊆ used := by
    intro hsubset
    have hcandidateCard := Finset.card_le_card hsubset
    omega
  obtain ⟨ideal, hideal, hunused⟩ := Finset.not_subset.mp hnotSubset
  refine ⟨ideal, hideal, ?_⟩
  intro span hspan heq
  apply hunused
  rw [Finset.mem_image]
  exact ⟨span, hspan, heq.symm⟩

/-- Transfer a candidate from its unique current owner to the hole, making
that owner the new hole.  The operation preserves membership and injectivity
without adding tagged copies of the ideal. -/
def FiniteCandidateHoleState.transferOwnedCandidate
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (ideal : Ideal) (hideal : ideal ∈ candidates state.hole)
    (owner : Span) (howner : owner ∈ block.erase state.hole)
    (howned : state.representative owner = ideal) :
    FiniteCandidateHoleState block candidates := by
  let transferred := Function.update state.representative state.hole ideal
  refine {
    hole := owner
    hole_mem := Finset.mem_of_mem_erase howner
    representative := transferred
    representative_mem := ?_
    representative_injective := ?_
  }
  · intro span hspan
    have hspanBlock : span ∈ block := Finset.mem_of_mem_erase hspan
    by_cases hspanHole : span = state.hole
    · subst span
      simpa [transferred, Function.update] using hideal
    · have hspanOld : span ∈ block.erase state.hole :=
          Finset.mem_erase.mpr ⟨hspanHole, hspanBlock⟩
      simpa [transferred, Function.update, hspanHole] using
        state.representative_mem span hspanOld
  · intro first hfirst second hsecond heq
    have hfirstBlock : first ∈ block := Finset.mem_of_mem_erase hfirst
    have hsecondBlock : second ∈ block := Finset.mem_of_mem_erase hsecond
    have hfirstOwner : first ≠ owner := (Finset.mem_erase.mp hfirst).1
    have hsecondOwner : second ≠ owner := (Finset.mem_erase.mp hsecond).1
    by_cases hfirstHole : first = state.hole
    · subst first
      by_cases hsecondHole : second = state.hole
      · exact hsecondHole.symm
      · have hsecondOld : second ∈ block.erase state.hole :=
          Finset.mem_erase.mpr ⟨hsecondHole, hsecondBlock⟩
        have hcollision : ideal = state.representative second := by
          simpa [transferred, Function.update, hsecondHole] using heq
        have heqOwner : owner = second := state.representative_injective
          howner hsecondOld (howned.trans hcollision)
        exact False.elim (hsecondOwner heqOwner.symm)
    · by_cases hsecondHole : second = state.hole
      · subst second
        have hfirstOld : first ∈ block.erase state.hole :=
          Finset.mem_erase.mpr ⟨hfirstHole, hfirstBlock⟩
        have hcollision : ideal = state.representative first := by
          simpa [transferred, Function.update, hfirstHole] using heq.symm
        have heqOwner : owner = first := state.representative_injective
          howner hfirstOld (howned.trans hcollision)
        exact False.elim (hfirstOwner heqOwner.symm)
      · apply state.representative_injective
        · exact Finset.mem_erase.mpr ⟨hfirstHole, hfirstBlock⟩
        · exact Finset.mem_erase.mpr ⟨hsecondHole, hsecondBlock⟩
        · simpa [transferred, Function.update, hfirstHole, hsecondHole]
            using heq

/-- After an ownership transfer, a sufficiently large candidate family at
the new hole is immediately fillable. -/
theorem FiniteCandidateHoleState.transferOwnedCandidate_canFill_of_card_lt
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (ideal : Ideal) (hideal : ideal ∈ candidates state.hole)
    (owner : Span) (howner : owner ∈ block.erase state.hole)
    (howned : state.representative owner = ideal)
    (hcard : (block.erase owner).card < (candidates owner).card) :
    (state.transferOwnedCandidate ideal hideal owner howner howned).CanFill := by
  exact FiniteCandidateHoleState.canFill_of_erase_card_lt_candidates_card
    (state.transferOwnedCandidate ideal hideal owner howner howned) hcard

/-- A fresh candidate of the displaced owner fills the transferred state.
This is the constructive kernel of a length-two augmenting path. -/
theorem FiniteCandidateHoleState.transferOwnedCandidate_canFill_of_fresh
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (ideal : Ideal) (hideal : ideal ∈ candidates state.hole)
    (owner : Span) (howner : owner ∈ block.erase state.hole)
    (howned : state.representative owner = ideal)
    (fresh : Ideal) (hfresh : fresh ∈ candidates owner)
    (hunused : ∀ span ∈ block.erase state.hole,
      fresh ≠ state.representative span) :
    (state.transferOwnedCandidate ideal hideal owner howner howned).CanFill := by
  refine ⟨fresh, hfresh, ?_⟩
  intro span hspan
  have hspanBlock : span ∈ block := Finset.mem_of_mem_erase hspan
  by_cases hspanHole : span = state.hole
  · subst span
    have hfreshIdeal : fresh ≠ ideal := by
      simpa [howned] using hunused owner howner
    simpa [FiniteCandidateHoleState.transferOwnedCandidate,
      Function.update] using hfreshIdeal
  · have hspanOld : span ∈ block.erase state.hole :=
      Finset.mem_erase.mpr ⟨hspanHole, hspanBlock⟩
    simpa [FiniteCandidateHoleState.transferOwnedCandidate,
      Function.update, hspanHole] using hunused span hspanOld

/-- A fillable one-hole state gives an SDR on the whole block. -/
theorem FiniteCandidateHoleState.hasDistinctRepresentatives_of_canFill
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hfill : state.CanFill) :
    FiniteCandidateHasDistinctRepresentativesOn block candidates := by
  obtain ⟨ideal, hideal, hunused⟩ := hfill
  let completed := Function.update state.representative state.hole ideal
  refine ⟨completed, ?_, ?_⟩
  · intro first hfirst second hsecond heq
    by_cases hfirstHole : first = state.hole
    · subst first
      by_cases hsecondHole : second = state.hole
      · exact hsecondHole.symm
      · have hsecondErase : second ∈ block.erase state.hole :=
          Finset.mem_erase.mpr ⟨hsecondHole, hsecond⟩
        have hcollision : ideal = state.representative second := by
          simpa [completed, Function.update, hsecondHole] using heq
        exact False.elim (hunused second hsecondErase hcollision)
    · by_cases hsecondHole : second = state.hole
      · subst second
        have hfirstErase : first ∈ block.erase state.hole :=
          Finset.mem_erase.mpr ⟨hfirstHole, hfirst⟩
        have hcollision : ideal = state.representative first := by
          simpa [completed, Function.update, hfirstHole] using heq.symm
        exact False.elim (hunused first hfirstErase hcollision)
      · apply state.representative_injective
        · exact Finset.mem_erase.mpr ⟨hfirstHole, hfirst⟩
        · exact Finset.mem_erase.mpr ⟨hsecondHole, hsecond⟩
        · simpa [completed, Function.update, hfirstHole, hsecondHole] using heq
  · intro span hspan
    by_cases hspanHole : span = state.hole
    · subst span
      simpa [completed, Function.update] using hideal
    · have hspanErase : span ∈ block.erase state.hole :=
        Finset.mem_erase.mpr ⟨hspanHole, hspan⟩
      simpa [completed, Function.update, hspanHole] using
        state.representative_mem span hspanErase

/-- A two-step augmenting exit supplies an SDR without any global matching,
Hall premise, or well-founded multi-step measure. -/
theorem FiniteCandidateHoleState.hasDistinctRepresentatives_of_twoStepAugmentingExit
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hexit : state.HasTwoStepAugmentingExit) :
    FiniteCandidateHasDistinctRepresentativesOn block candidates := by
  obtain ⟨ideal, hideal, owner, howner, howned, fresh, hfresh, hunused⟩ := hexit
  let next :=
    state.transferOwnedCandidate ideal hideal owner howner howned
  exact next.hasDistinctRepresentatives_of_canFill
    (state.transferOwnedCandidate_canFill_of_fresh
      ideal hideal owner howner howned fresh hfresh hunused)

/-- The same two-step augmenting certificate proves the block Hall
inequality. -/
theorem FiniteCandidateHoleState.card_le_biUnion_of_twoStepAugmentingExit
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hexit : state.HasTwoStepAugmentingExit) :
    block.card ≤ (block.biUnion candidates).card := by
  obtain ⟨representative, hinjective, hmem⟩ :=
    state.hasDistinctRepresentatives_of_twoStepAugmentingExit hexit
  exact Finset.card_le_biUnion_card_of_injective_mem block candidates
    representative hmem hinjective

/-- Owner-star expansion completes every one-hole state, directly when
possible and otherwise through the forced two-step exit. -/
theorem FiniteCandidateHoleState.hasDistinctRepresentatives_of_ownerStarExpansion
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hexpand : block.card ≤ state.ownerStar.card) :
    FiniteCandidateHasDistinctRepresentativesOn block candidates := by
  by_cases hfill : state.CanFill
  · exact state.hasDistinctRepresentatives_of_canFill hfill
  · exact state.hasDistinctRepresentatives_of_twoStepAugmentingExit
      (state.hasTwoStepAugmentingExit_of_ownerStarExpansion hfill hexpand)

/-- Owner-star expansion implies the block Hall inequality for the current
one-hole state. -/
theorem FiniteCandidateHoleState.card_le_biUnion_of_ownerStarExpansion
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hexpand : block.card ≤ state.ownerStar.card) :
    block.card ≤ (block.biUnion candidates).card := by
  obtain ⟨representative, hinjective, hmem⟩ :=
    state.hasDistinctRepresentatives_of_ownerStarExpansion hexpand
  exact Finset.card_le_biUnion_card_of_injective_mem block candidates
    representative hmem hinjective

/-- The state-free feasible-owner expansion profile completes every one-hole
state on the candidate system. -/
theorem FiniteCandidateHoleState.hasDistinctRepresentatives_of_feasibleOwnerStarExpansion
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hprofile : FiniteCandidateFeasibleOwnerStarExpansion block candidates) :
    FiniteCandidateHasDistinctRepresentativesOn block candidates := by
  by_cases hfill : state.CanFill
  · exact state.hasDistinctRepresentatives_of_canFill hfill
  · exact state.hasDistinctRepresentatives_of_twoStepAugmentingExit
      (state.hasTwoStepAugmentingExit_of_feasibleOwnerStarExpansion
        hprofile hfill)

/-- The same feasible-owner profile implies the block Hall inequality once a
one-hole state is supplied. -/
theorem FiniteCandidateHoleState.card_le_biUnion_of_feasibleOwnerStarExpansion
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hprofile : FiniteCandidateFeasibleOwnerStarExpansion block candidates) :
    block.card ≤ (block.biUnion candidates).card := by
  obtain ⟨representative, hinjective, hmem⟩ :=
    state.hasDistinctRepresentatives_of_feasibleOwnerStarExpansion hprofile
  exact Finset.card_le_biUnion_card_of_injective_mem block candidates
    representative hmem hinjective

/-- A proof that the local owner-star cannot close supplies an SDR on the
whole block.  The remaining open work is to derive this premise from genuine
reflected frontier geometry. -/
theorem FiniteCandidateHoleState.hasDistinctRepresentatives_of_not_closedStar
    {Span Ideal : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hnotClosed : ¬ state.HasClosedSaturatedOwnerStar) :
    FiniteCandidateHasDistinctRepresentativesOn block candidates := by
  rcases state.canFill_or_hasTwoStepAugmentingExit_of_not_closedStar hnotClosed with
    hfill | hexit
  · exact state.hasDistinctRepresentatives_of_canFill hfill
  · exact state.hasDistinctRepresentatives_of_twoStepAugmentingExit hexit

/-- Excluding the local closed-star obstruction implies the block Hall
inequality. -/
theorem FiniteCandidateHoleState.card_le_biUnion_of_not_closedStar
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (state : FiniteCandidateHoleState block candidates)
    (hnotClosed : ¬ state.HasClosedSaturatedOwnerStar) :
    block.card ≤ (block.biUnion candidates).card := by
  obtain ⟨representative, hinjective, hmem⟩ :=
    state.hasDistinctRepresentatives_of_not_closedStar hnotClosed
  exact Finset.card_le_biUnion_card_of_injective_mem block candidates
    representative hmem hinjective

/-- Under the singleton-or-block-large profile, every one-hole state fills
directly or after one ownership transfer.  No candidate priority, matching,
or multi-step descent measure is needed. -/
theorem FiniteCandidateHoleState.hasDistinctRepresentatives_of_singletonOrBlockLarge
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (hprofile : SingletonOrBlockLarge block candidates)
    (howners : SingletonCandidateOwnersBlockLarge block candidates)
    (state : FiniteCandidateHoleState block candidates) :
    FiniteCandidateHasDistinctRepresentativesOn block candidates := by
  by_cases hfill : state.CanFill
  · exact state.hasDistinctRepresentatives_of_canFill hfill
  · have hblockPositive : 0 < block.card :=
      Finset.card_pos.mpr ⟨state.hole, state.hole_mem⟩
    have heraseLt : (block.erase state.hole).card < block.card := by
      rw [Finset.card_erase_of_mem state.hole_mem]
      omega
    rcases hprofile state.hole state.hole_mem with hsingleton | hlarge
    · obtain ⟨ideal, hfamily⟩ := Finset.card_eq_one.mp hsingleton
      have hideal : ideal ∈ candidates state.hole := by
        simp [hfamily]
      have hused : ∃ owner ∈ block.erase state.hole,
          state.representative owner = ideal := by
        by_contra hnone
        push Not at hnone
        exact hfill ⟨ideal, hideal, fun owner howner ↦
          (hnone owner howner).symm⟩
      obtain ⟨owner, howner, howned⟩ := hused
      have hownerLarge : block.card ≤ (candidates owner).card :=
        howners state.hole state.hole_mem ideal hfamily owner howner
          (howned ▸ state.representative_mem owner howner)
      have hownerEraseLt : (block.erase owner).card <
          (candidates owner).card := by
        have hownerMem : owner ∈ block := Finset.mem_of_mem_erase howner
        rw [Finset.card_erase_of_mem hownerMem]
        omega
      let next :=
        state.transferOwnedCandidate ideal hideal owner howner howned
      exact next.hasDistinctRepresentatives_of_canFill
        (state.transferOwnedCandidate_canFill_of_card_lt
          ideal hideal owner howner howned hownerEraseLt)
    · have : state.CanFill :=
        state.canFill_of_erase_card_lt_candidates_card (by omega)
      exact False.elim (hfill this)

/-- The reviewed one-transfer profile implies the block Hall inequality. -/
theorem FiniteCandidateHoleState.card_le_biUnion_of_singletonOrBlockLarge
    {Span Ideal : Type*} [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (hprofile : SingletonOrBlockLarge block candidates)
    (howners : SingletonCandidateOwnersBlockLarge block candidates)
    (state : FiniteCandidateHoleState block candidates) :
    block.card ≤ (block.biUnion candidates).card := by
  obtain ⟨representative, hinjective, hmem⟩ :=
    state.hasDistinctRepresentatives_of_singletonOrBlockLarge
      hprofile howners
  exact Finset.card_le_biUnion_card_of_injective_mem block candidates
    representative hmem hinjective

/-- The stronger block-large reached-owner profile specialized to every
genuine reflected endpoint block. Experiment 0042 tests this exact shape at
the frozen `n = 12`, `k = 7` root; the arbitrary theorem remains open. -/
def AllocatedReflectedEndpointRankTransitionFeasibleOwnerHasBlockLargeFamily
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k) : Prop :=
  ∀ first last : AllocatedExactRankFrontierSpan
      chi lower upper color rank,
    FiniteCandidateFeasibleOwnerHasBlockLargeFamily
      (allocatedExactRankFrontierBlock first last)
      (allocatedReflectedEndpointRankTransitionCandidates
        chi lower upper color hrank hrankTop)

/-- The state-free owner-map expansion profile specialized to every genuine
reflected endpoint block.  Experiment 0041 tests this exact shape at the
frozen `n = 12`, `k = 7` root; the arbitrary theorem remains open. -/
def AllocatedReflectedEndpointRankTransitionFeasibleOwnerStarExpansion
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k) : Prop :=
  ∀ first last : AllocatedExactRankFrontierSpan
      chi lower upper color rank,
    FiniteCandidateFeasibleOwnerStarExpansion
      (allocatedExactRankFrontierBlock first last)
      (allocatedReflectedEndpointRankTransitionCandidates
        chi lower upper color hrank hrankTop)

/-- A block-large reached owner in every genuine reflected block supplies the
corresponding owner-star expansion profile. -/
theorem
    allocatedReflectedEndpointRankTransitionFeasibleOwnerStarExpansion_of_blockLargeFamily
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    {hrank : 1 ≤ rank} {hrankTop : rank < k}
    (hlarge :
      AllocatedReflectedEndpointRankTransitionFeasibleOwnerHasBlockLargeFamily
        chi lower upper color hrank hrankTop) :
    AllocatedReflectedEndpointRankTransitionFeasibleOwnerStarExpansion
      chi lower upper color hrank hrankTop := by
  intro first last
  exact finiteCandidateFeasibleOwnerStarExpansion_of_blockLargeFamily
    (hlarge first last)

/-- The separate induction input needed downstream: every nonempty endpoint
block already has a partial injection with one hole.  This is not supplied by
owner-star expansion itself. -/
def AllocatedReflectedEndpointRankTransitionOneHoleStateExists
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k) : Prop :=
  ∀ first last : AllocatedExactRankFrontierSpan
      chi lower upper color rank,
    let spans := allocatedExactRankFrontierBlock first last
    spans.Nonempty →
      Nonempty (FiniteCandidateHoleState spans
        (allocatedReflectedEndpointRankTransitionCandidates
          chi lower upper color hrank hrankTop))

/-- Feasible-owner-star expansion proves consecutive-block expansion once the
inductively supplied one-hole states are available.  The two premises expose
the geometric escape and induction-construction obligations separately. -/
theorem allocatedReflectedEndpointRankTransitionBlockExpansion_of_feasibleOwnerStar
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (hstar : AllocatedReflectedEndpointRankTransitionFeasibleOwnerStarExpansion
      chi lower upper color hrank hrankTop)
    (hstates : AllocatedReflectedEndpointRankTransitionOneHoleStateExists
      chi lower upper color hrank hrankTop) :
    AllocatedReflectedEndpointRankTransitionBlockExpansion
      chi lower upper color hrank hrankTop := by
  intro first last
  let spans := allocatedExactRankFrontierBlock first last
  change spans.card ≤
    (spans.biUnion (allocatedReflectedEndpointRankTransitionCandidates
      chi lower upper color hrank hrankTop)).card
  by_cases hne : spans.Nonempty
  · let state := Classical.choice (hstates first last hne)
    exact state.card_le_biUnion_of_feasibleOwnerStarExpansion
      (hstar first last)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- The stronger block-large reached-owner profile proves block expansion once
the separate one-hole-state induction premise is available. -/
theorem allocatedReflectedEndpointRankTransitionBlockExpansion_of_blockLargeFamily
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (hlarge :
      AllocatedReflectedEndpointRankTransitionFeasibleOwnerHasBlockLargeFamily
        chi lower upper color hrank hrankTop)
    (hstates : AllocatedReflectedEndpointRankTransitionOneHoleStateExists
      chi lower upper color hrank hrankTop) :
    AllocatedReflectedEndpointRankTransitionBlockExpansion
      chi lower upper color hrank hrankTop :=
  allocatedReflectedEndpointRankTransitionBlockExpansion_of_feasibleOwnerStar
    hrank hrankTop
    (allocatedReflectedEndpointRankTransitionFeasibleOwnerStarExpansion_of_blockLargeFamily
      hlarge)
    hstates

/-- Every unfillable state has an allowed successor with strictly smaller
measure.  The relation on measures is kept explicit rather than fixed to
natural-number order. -/
def StrictFiniteCandidateHoleProgress
    {Span Ideal Measure : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (move : FiniteCandidateHoleState block candidates →
      FiniteCandidateHoleState block candidates → Prop)
    (measure : FiniteCandidateHoleState block candidates → Measure)
    (decreases : Measure → Measure → Prop) : Prop :=
  ∀ state, ¬ state.CanFill →
    ∃ next, move state next ∧
      decreases (measure next) (measure state)

/-- A well-founded strict descent from every unfillable one-hole state must
terminate at a fillable state, hence supplies an SDR for the whole block. -/
theorem FiniteCandidateHoleState.hasDistinctRepresentatives_of_strictProgress
    {Span Ideal Measure : Type*} [DecidableEq Span]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (move : FiniteCandidateHoleState block candidates →
      FiniteCandidateHoleState block candidates → Prop)
    (measure : FiniteCandidateHoleState block candidates → Measure)
    (decreases : Measure → Measure → Prop)
    (hwellFounded : WellFounded decreases)
    (hprogress : StrictFiniteCandidateHoleProgress
      move measure decreases)
    (state : FiniteCandidateHoleState block candidates) :
    FiniteCandidateHasDistinctRepresentativesOn block candidates := by
  induction state using
      (WellFounded.onFun (f := measure) hwellFounded).induction with
  | h state ih =>
      by_cases hfill : state.CanFill
      · exact state.hasDistinctRepresentatives_of_canFill hfill
      · obtain ⟨next, _, hdecrease⟩ := hprogress state hfill
        exact ih next hdecrease

/-- The same descent mechanism proves the Hall inequality for the block. -/
theorem FiniteCandidateHoleState.card_le_biUnion_of_strictProgress
    {Span Ideal Measure : Type*}
    [DecidableEq Span] [DecidableEq Ideal]
    {block : Finset Span} {candidates : Span → Finset Ideal}
    (move : FiniteCandidateHoleState block candidates →
      FiniteCandidateHoleState block candidates → Prop)
    (measure : FiniteCandidateHoleState block candidates → Measure)
    (decreases : Measure → Measure → Prop)
    (hwellFounded : WellFounded decreases)
    (hprogress : StrictFiniteCandidateHoleProgress
      move measure decreases)
    (state : FiniteCandidateHoleState block candidates) :
    block.card ≤ (block.biUnion candidates).card := by
  obtain ⟨representative, hinjective, hmem⟩ :=
    state.hasDistinctRepresentatives_of_strictProgress
      move measure decreases hwellFounded hprogress
  exact Finset.card_le_biUnion_card_of_injective_mem block candidates
    representative hmem hinjective

end ErdosSzekeres

end
