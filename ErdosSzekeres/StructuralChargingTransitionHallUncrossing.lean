module

public import ErdosSzekeres.StructuralChargingTransitionHallBlocks

@[expose] public section

/-!
# Limits of pairwise meet/join uncrossing

The reflected two-endpoint candidates live in a finite distributive lattice.
A first local gate asks whether representatives of adjacent spans can be
replaced by their meet and join in one of the two possible assignments.

This file isolates that generic local property and proves that it is too weak
to yield Hall expansion, even when every two candidate families expand.  Any
successful use of the property must therefore add a genuinely higher-order
frontier invariant or a well-founded augmentation argument.
-/

namespace ErdosSzekeres

/-- Two candidate families flexibly uncross when each pair of representatives
can be replaced by meet and join in at least one of the two assignments. -/
def FlexibleMeetJoinUncrossing
    {Ideal : Type*} [Lattice Ideal] [DecidableEq Ideal]
    (first second : Finset Ideal) : Prop :=
  ∀ a ∈ first, ∀ b ∈ second,
    ((a ⊓ b ∈ first ∧ a ⊔ b ∈ second) ∨
      (a ⊔ b ∈ first ∧ a ⊓ b ∈ second))

/-- Every two distinct candidate families have a union of size at least two. -/
def CandidatePairExpansion
    {ι Ideal : Type*} [DecidableEq Ideal]
    (candidates : ι → Finset Ideal) : Prop :=
  ∀ i j, i ≠ j → 2 ≤ (candidates i ∪ candidates j).card

/-- A system of distinct representatives for a finite candidate family. -/
def FiniteCandidateHasDistinctRepresentatives
    {ι Ideal : Type*} (candidates : ι → Finset Ideal) : Prop :=
  ∃ representative : ι → Ideal,
    Function.Injective representative ∧
      ∀ i, representative i ∈ candidates i

/-- The smallest abstract obstruction: three spans all see the same two
ideals. -/
def threeSpansTwoIdeals : Fin 3 → Finset (Fin 2) :=
  fun _ ↦ Finset.univ

/-- The two-ideal family is itself one honest lattice transition interval. -/
theorem twoIdealTransitionLane_eq_univ :
    pascalTransitionInterval (0 : Fin 2) 1 = Finset.univ := by
  ext ideal
  fin_cases ideal <;> simp [pascalTransitionInterval]

/-- Both proof-side lanes may be the same transition interval without adding
any representative state. -/
theorem threeSpansTwoIdeals_twoLane_interval (i : Fin 3) :
    threeSpansTwoIdeals i =
      pascalTransitionInterval (0 : Fin 2) 1 ∪
        pascalTransitionInterval (0 : Fin 2) 1 := by
  rw [twoIdealTransitionLane_eq_univ]
  simp [threeSpansTwoIdeals]

/-- Flexible meet/join closure, even together with every two-family Hall test,
does not imply a system of distinct representatives.  A higher-order frontier
invariant is necessary. -/
theorem flexibleMeetJoin_pairExpansion_not_sufficient :
    (∀ i j, FlexibleMeetJoinUncrossing
      (threeSpansTwoIdeals i) (threeSpansTwoIdeals j)) ∧
    CandidatePairExpansion threeSpansTwoIdeals ∧
    ¬ FiniteCandidateHasDistinctRepresentatives threeSpansTwoIdeals := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FlexibleMeetJoinUncrossing, threeSpansTwoIdeals]
  · simp [CandidatePairExpansion, threeSpansTwoIdeals]
  · rintro ⟨representative, hinjective, _⟩
    have hcard := Fintype.card_le_of_injective representative hinjective
    norm_num at hcard

end ErdosSzekeres

end
