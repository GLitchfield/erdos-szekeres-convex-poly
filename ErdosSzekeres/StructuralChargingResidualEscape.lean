module

public import ErdosSzekeres.StructuralChargingWitnessBranches

@[expose] public section

/-!
# Parameter-uniform residual escape from deletion packing

The packed `(5,6,7)` branch deletes one vertex from each of two disjoint
carriers and an arbitrary block from their complement.  This file separates
the finite-set mechanism from those particular cardinalities.
-/

namespace ErdosSzekeres

/-- Hereditary off-diagonal state for arbitrary one-change colorings.  This is
stronger than `DecomposableStateUpper` and is the exact input needed to obtain
deletion packing on an ordered two-side union. -/
def OneChangeStateUpper (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)},
    OneChangeOn χ support → decomposableThreshold a u k < support.card →
      ContainsCapSet χ support a ∨ ContainsCupSet χ support u ∨
        ContainsStrongPolygonSet χ support k

/-- A deletion-packing condition with independent deletion and witness
cardinalities. -/
def StrongPolygonAvoidsEveryDeletion {n : ℕ} (χ : TripleColoring n)
    (ambient : Finset (Fin n)) (deleteCard witnessCard : ℕ) : Prop :=
  ∀ deleted : Finset (Fin n), deleted ⊆ ambient → deleted.card = deleteCard →
    ContainsStrongPolygonSet χ (ambient \ deleted) witnessCard

/-- A hereditary one-change predecessor state supplies uniform deletion
packing whenever every deletion leaves more than its threshold. -/
theorem strongPolygonAvoidsEveryDeletion_of_oneChangeStateUpper
    {n a u k deleteCard : ℕ} {χ : TripleColoring n}
    {ambient : Finset (Fin n)}
    (hstate : OneChangeStateUpper a u k)
    (hone : OneChangeOn χ ambient)
    (hcard : decomposableThreshold a u k + 1 + deleteCard ≤ ambient.card)
    (hnoCap : ¬ContainsCapSet χ ambient a)
    (hnoCup : ¬ContainsCupSet χ ambient u) :
    StrongPolygonAvoidsEveryDeletion χ ambient deleteCard k := by
  intro deleted hdeletedSub hdeletedCard
  have hremainingCard :
      decomposableThreshold a u k < (ambient \ deleted).card := by
    have hcardSplit := Finset.card_sdiff_add_card_eq_card hdeletedSub
    omega
  rcases hstate (hone.mono Finset.sdiff_subset) hremainingCard with
      hcap | hcup | hstrong
  · exact (hnoCap
      (FinsetPolygon.ContainsCapSet.mono hcap Finset.sdiff_subset)).elim
  · exact (hnoCup
      (FinsetPolygon.ContainsCupSet.mono hcup Finset.sdiff_subset)).elim
  · exact hstrong

/-- The residual escape data left by two disjoint equal-cardinality carriers.
One vertex is deleted from each carrier together with an arbitrary residual
block. -/
def PairResidualEscape {n : ℕ} (χ : TripleColoring n)
    (ambient first second : Finset (Fin n))
    (residualCard blockCard witnessCard : ℕ) : Prop :=
  let residual := ambient \ (first ∪ second)
  residual.card = residualCard ∧
    ∀ a ∈ first, ∀ b ∈ second,
      ∀ block : Finset (Fin n), block ⊆ residual → block.card = blockCard →
        ContainsStrongPolygonSet χ
          (ambient \ insert a (insert b block)) witnessCard

/-- Generic finite-set extraction of a pair-residual escape from deletion
packing. -/
theorem pairResidualEscape_of_avoidsEveryDeletion
    {n carrierCard residualCard blockCard witnessCard : ℕ}
    {χ : TripleColoring n} {ambient first second : Finset (Fin n)}
    (hambientCard : ambient.card = carrierCard + carrierCard + residualCard)
    (hfirstSub : first ⊆ ambient) (hsecondSub : second ⊆ ambient)
    (hdisjoint : Disjoint first second)
    (hfirstCard : first.card = carrierCard)
    (hsecondCard : second.card = carrierCard)
    (hpacking : StrongPolygonAvoidsEveryDeletion χ ambient (blockCard + 2) witnessCard) :
    PairResidualEscape χ ambient first second residualCard blockCard witnessCard := by
  have hpairSub : first ∪ second ⊆ ambient :=
    Finset.union_subset hfirstSub hsecondSub
  have hpairCard : (first ∪ second).card = carrierCard + carrierCard := by
    rw [Finset.card_union_of_disjoint hdisjoint, hfirstCard, hsecondCard]
  refine ⟨?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hpairSub, hambientCard, hpairCard]
    omega
  · intro a haFirst b hbSecond block hblockSub hblockCard
    have haAmbient : a ∈ ambient := hfirstSub haFirst
    have hbAmbient : b ∈ ambient := hsecondSub hbSecond
    have hblockAmbient : block ⊆ ambient :=
      hblockSub.trans Finset.sdiff_subset
    have hab : a ≠ b := by
      intro hab
      subst b
      exact Finset.disjoint_left.mp hdisjoint haFirst hbSecond
    have haBlock : a ∉ block := by
      intro ha
      have haResidual := hblockSub ha
      exact (Finset.mem_sdiff.mp haResidual).2
        (Finset.mem_union_left second haFirst)
    have hbBlock : b ∉ block := by
      intro hb
      have hbResidual := hblockSub hb
      exact (Finset.mem_sdiff.mp hbResidual).2
        (Finset.mem_union_right first hbSecond)
    apply hpacking (insert a (insert b block))
    · exact Finset.insert_subset haAmbient
        (Finset.insert_subset hbAmbient hblockAmbient)
    · simp [hab, haBlock, hbBlock, hblockCard]

/-- Unpack a concrete strong-polygon witness from the generic residual escape
state. -/
theorem PairResidualEscape.exists_witness
    {n residualCard blockCard witnessCard : ℕ}
    {χ : TripleColoring n} {ambient first second block : Finset (Fin n)}
    {a b : Fin n}
    (hescape :
      PairResidualEscape χ ambient first second residualCard blockCard witnessCard)
    (ha : a ∈ first) (hb : b ∈ second)
    (hblockSub : block ⊆ ambient \ (first ∪ second))
    (hblockCard : block.card = blockCard) :
    ∃ third : Finset (Fin n),
      third ⊆ ambient \ insert a (insert b block) ∧
        third.card = witnessCard ∧ IsStrongPolygonSet χ third := by
  exact hescape.2 a ha b hb block hblockSub hblockCard

/-- A residual-only witness with the complementary cardinality is exactly the
unused part of the residual. -/
theorem residualWitness_eq_residual_sdiff
    {n residualCard blockCard witnessCard : ℕ}
    {ambient first second block third : Finset (Fin n)} {a b : Fin n}
    (hresidualCard : (ambient \ (first ∪ second)).card = residualCard)
    (hblockSub : block ⊆ ambient \ (first ∪ second))
    (hblockCard : block.card = blockCard)
    (hthirdSub : third ⊆ ambient \ insert a (insert b block))
    (hthirdCard : third.card = witnessCard)
    (hthirdFirst : Disjoint third first)
    (hthirdSecond : Disjoint third second)
    (hbalance : residualCard = blockCard + witnessCard) :
    third = (ambient \ (first ∪ second)) \ block := by
  have hsubset : third ⊆ (ambient \ (first ∪ second)) \ block := by
    intro x hxThird
    have hxDeleted := Finset.mem_sdiff.mp (hthirdSub hxThird)
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_sdiff.mpr
      constructor
      · exact hxDeleted.1
      · intro hxPair
        rcases Finset.mem_union.mp hxPair with hxFirst | hxSecond
        · exact Finset.disjoint_left.mp hthirdFirst hxThird hxFirst
        · exact Finset.disjoint_left.mp hthirdSecond hxThird hxSecond
    · intro hxBlock
      exact hxDeleted.2 (by simp [hxBlock])
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [Finset.card_sdiff_of_subset hblockSub, hresidualCard, hblockCard,
    hthirdCard]
  omega

/-- Uniform first residual leaf: if the unused residual complement is not
strong and the residual cardinality splits exactly into the deleted block and
the replacement witness, every packed replacement must touch at least one of
the two carriers. -/
theorem PairResidualEscape.exists_carrierTouching_witness
    {n residualCard blockCard witnessCard : ℕ}
    {χ : TripleColoring n} {ambient first second block : Finset (Fin n)}
    {a b : Fin n}
    (hescape :
      PairResidualEscape χ ambient first second residualCard blockCard witnessCard)
    (ha : a ∈ first) (hb : b ∈ second)
    (hblockSub : block ⊆ ambient \ (first ∪ second))
    (hblockCard : block.card = blockCard)
    (hbalance : residualCard = blockCard + witnessCard)
    (hcomplementNotStrong :
      ¬IsStrongPolygonSet χ ((ambient \ (first ∪ second)) \ block)) :
    ∃ third : Finset (Fin n),
      third ⊆ ambient \ insert a (insert b block) ∧
        third.card = witnessCard ∧ IsStrongPolygonSet χ third ∧
          (¬Disjoint third first ∨ ¬Disjoint third second) := by
  obtain ⟨third, hthirdSub, hthirdCard, hthirdStrong⟩ :=
    hescape.exists_witness ha hb hblockSub hblockCard
  by_cases hthirdFirst : Disjoint third first
  · by_cases hthirdSecond : Disjoint third second
    · have heq := residualWitness_eq_residual_sdiff hescape.1 hblockSub
        hblockCard hthirdSub hthirdCard hthirdFirst hthirdSecond hbalance
      exact (hcomplementNotStrong (heq ▸ hthirdStrong)).elim
    · exact ⟨third, hthirdSub, hthirdCard, hthirdStrong, Or.inr hthirdSecond⟩
  · exact ⟨third, hthirdSub, hthirdCard, hthirdStrong, Or.inl hthirdFirst⟩

/-- The existing sharp-boundary packing condition is exactly the
`deleteCard = witnessCard = 6` specialization. -/
theorem strongPolygonAvoidsEveryDeletion_six_iff
    {n : ℕ} {χ : TripleColoring n} {ambient : Finset (Fin n)} :
    StrongPolygonAvoidsEveryDeletion χ ambient 6 6 ↔
      StrongSixAvoidsEverySix χ ambient := by
  rfl

end ErdosSzekeres
