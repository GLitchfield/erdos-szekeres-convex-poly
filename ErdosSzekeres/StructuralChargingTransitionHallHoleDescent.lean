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

/-- A system of distinct representatives restricted to one finite block. -/
def FiniteCandidateHasDistinctRepresentativesOn
    {Span Ideal : Type*} (block : Finset Span)
    (candidates : Span → Finset Ideal) : Prop :=
  ∃ representative : Span → Ideal,
    Set.InjOn representative block ∧
      ∀ span ∈ block, representative span ∈ candidates span

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
