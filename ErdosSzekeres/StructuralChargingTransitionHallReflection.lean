module

public import ErdosSzekeres.StructuralChargingTransitionHall

@[expose] public section

/-!
# Orientation-reflected endpoint-transition candidates

The rotate-complement involution on rectangular lower ideals induces reversal
of their boundary-path slots.  It therefore permutes the existing Pascal-slot
carrier without adding an orientation tag or increasing capacity.

For a span crossing one allocated split, this file leaves its endpoint
transition candidates unchanged when the left endpoint belongs to the lower
child and rotate-complements every candidate in the opposite orientation.
The resulting Hall condition still constructs an injection into exactly the
adjacent Pascal layer.  Whether that reflected Hall condition follows from
deep-below incidence is a separate, geometry-specific question.
-/

namespace ErdosSzekeres

noncomputable section

namespace PascalGridIdeal

/-- Rotate a rectangular ideal by 180 degrees and complement its cells. -/
def reflectedComplement {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) : PascalGridIdeal rows columns where
  cells := Finset.univ.filter fun cell ↦
    (cell.1.rev, cell.2.rev) ∉ ideal.cells
  isLowerSet := by
    intro larger smaller hle hlarger
    rw [Finset.mem_coe, Finset.mem_filter] at hlarger ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hsmaller
    apply hlarger.2
    apply ideal.isLowerSet ?_ hsmaller
    exact ⟨Fin.rev_le_rev.mpr hle.1, Fin.rev_le_rev.mpr hle.2⟩

@[simp] theorem mem_reflectedComplement {rows columns : ℕ}
    {ideal : PascalGridIdeal rows columns}
    {cell : Fin rows × Fin columns} :
    cell ∈ (reflectedComplement ideal).cells ↔
      (cell.1.rev, cell.2.rev) ∉ ideal.cells := by
  simp [reflectedComplement]

/-- Rotate-complement is an involution on the same ideal lattice. -/
@[simp] theorem reflectedComplement_involutive {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) :
    reflectedComplement (reflectedComplement ideal) = ideal := by
  ext cell
  simp only [mem_reflectedComplement, Fin.rev_rev, not_not]

/-- Rotate-complement reverses inclusion of rectangular ideals. -/
theorem reflectedComplement_antitone {rows columns : ℕ} :
    Antitone (@reflectedComplement rows columns) := by
  intro first second hfirstSecond
  change (reflectedComplement second).cells ⊆
    (reflectedComplement first).cells
  intro cell hcell
  rw [mem_reflectedComplement] at hcell ⊢
  intro hfirst
  exact hcell (hfirstSecond hfirst)

@[simp] theorem reflectedComplement_inf {rows columns : ℕ}
    (first second : PascalGridIdeal rows columns) :
    reflectedComplement (first ⊓ second) =
      reflectedComplement first ⊔ reflectedComplement second := by
  classical
  ext cell
  simp only [mem_reflectedComplement]
  change (cell.1.rev, cell.2.rev) ∉ first.cells ∩ second.cells ↔
    cell ∈ (reflectedComplement first).cells ∪
      (reflectedComplement second).cells
  by_cases hfirst : (cell.1.rev, cell.2.rev) ∈ first.cells <;>
    simp [hfirst]

@[simp] theorem reflectedComplement_sup {rows columns : ℕ}
    (first second : PascalGridIdeal rows columns) :
    reflectedComplement (first ⊔ second) =
      reflectedComplement first ⊓ reflectedComplement second := by
  ext cell
  simp only [mem_reflectedComplement]
  change (cell.1.rev, cell.2.rev) ∉ first.cells ∪ second.cells ↔
    cell ∈ (reflectedComplement first).cells ∩
      (reflectedComplement second).cells
  simp

/-- Rotate-complement carries a lattice interval to the interval between the
reflected endpoints. -/
@[simp] theorem reflectedComplement_mem_pascalTransitionInterval_iff
    {rows columns : ℕ} {first second state : PascalGridIdeal rows columns} :
    reflectedComplement state ∈
        pascalTransitionInterval (reflectedComplement first)
          (reflectedComplement second) ↔
      state ∈ pascalTransitionInterval first second := by
  simp only [pascalTransitionInterval, Finset.mem_filter, Finset.mem_univ,
    true_and, ← reflectedComplement_sup, ← reflectedComplement_inf]
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · simpa using reflectedComplement_antitone hupper
    · simpa using reflectedComplement_antitone hlower
  · rintro ⟨hlower, hupper⟩
    exact ⟨reflectedComplement_antitone hupper,
      reflectedComplement_antitone hlower⟩

/-- Rotate-complement as a same-carrier equivalence. -/
def reflectedComplementEquiv (rows columns : ℕ) :
    PascalGridIdeal rows columns ≃ PascalGridIdeal rows columns where
  toFun := reflectedComplement
  invFun := reflectedComplement
  left_inv := reflectedComplement_involutive
  right_inv := reflectedComplement_involutive

theorem reflectedComplement_rowLength {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) (i : Fin rows) :
    (reflectedComplement ideal).rowLength i =
      columns - ideal.rowLength i.rev := by
  have hrow :
      (reflectedComplement ideal).row i =
        Finset.univ \ (ideal.row i.rev).map Fin.revPerm.toEmbedding := by
    ext j
    simp [row, reflectedComplement]
  rw [rowLength, hrow, Finset.card_sdiff]
  simp [rowLength]

@[simp] theorem reflectedComplement_boundaryIndex {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) (i : Fin rows) :
    (reflectedComplement ideal).boundaryIndex i =
      (ideal.boundaryIndex i.rev).rev := by
  apply Fin.ext
  simp only [boundaryIndex, reflectedComplement_rowLength, Fin.val_rev]
  have hrow := ideal.rowLength_le i.rev
  have hi := i.isLt
  omega

/-- Reverse every position in a fixed-cardinality boundary slot. -/
def boundarySlotReversal (rows columns : ℕ) :
    {indices : Finset (Fin (rows + columns)) // indices.card = rows} ≃
      {indices : Finset (Fin (rows + columns)) // indices.card = rows} :=
  Equiv.subtypeEquiv (Equiv.finsetCongr Fin.revPerm) (by
    intro indices
    simp)

/-- Rotate-complementing an ideal reverses its boundary-path slot. -/
theorem boundarySlot_reflectedComplement {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) :
    boundarySlot (reflectedComplement ideal) =
      boundarySlotReversal rows columns (boundarySlot ideal) := by
  apply Subtype.ext
  ext index
  simp only [boundarySlot, boundarySlotReversal, Equiv.subtypeEquiv_apply,
    Equiv.finsetCongr_apply, Finset.mem_map, Finset.mem_univ, true_and,
    Equiv.toEmbedding_apply, Fin.revPerm_apply, boundaryEmbedding]
  constructor
  · rintro ⟨i, hi⟩
    change (reflectedComplement ideal).boundaryIndex i = index at hi
    refine ⟨ideal.boundaryIndex i.rev, ⟨i.rev, rfl⟩, ?_⟩
    rw [reflectedComplement_boundaryIndex] at hi
    exact hi
  · rintro ⟨slot, ⟨i, hiSlot⟩, hi⟩
    change ideal.boundaryIndex i = slot at hiSlot
    subst slot
    refine ⟨i.rev, ?_⟩
    change (reflectedComplement ideal).boundaryIndex i.rev = index
    rw [reflectedComplement_boundaryIndex]
    simpa only [Fin.rev_rev] using hi

end PascalGridIdeal

/-- Reversal is a permutation of the existing, untagged allocated slots. -/
def allocatedPascalSlotReversal (rank k : ℕ) :
    AllocatedPascalSlot rank k ≃ AllocatedPascalSlot rank k :=
  Equiv.subtypeEquiv (Equiv.finsetCongr Fin.revPerm) (by
    intro indices
    simp)

/-- The rank-specialized ideal encoding intertwines rotate-complement and slot
reversal.  In particular, reflection does not enlarge the slot carrier. -/
theorem rankIdealSlotEmbedding_reflectedComplement {rank k : ℕ}
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (ideal : PascalGridIdeal (rank - 1) (k - rank - 1)) :
    PascalGridIdeal.rankIdealSlotEmbedding hrank hrankTop
        (PascalGridIdeal.reflectedComplement ideal) =
      allocatedPascalSlotReversal rank k
        (PascalGridIdeal.rankIdealSlotEmbedding hrank hrankTop ideal) := by
  let hsize := PascalGridIdeal.rankRectangle_add_eq hrank hrankTop
  change PascalGridIdeal.finsetCardCongr hsize
      (PascalGridIdeal.boundarySlot (PascalGridIdeal.reflectedComplement ideal)) =
    allocatedPascalSlotReversal rank k
      (PascalGridIdeal.finsetCardCongr hsize (PascalGridIdeal.boundarySlot ideal))
  rw [PascalGridIdeal.boundarySlot_reflectedComplement]
  apply Subtype.ext
  ext index
  simp only [PascalGridIdeal.finsetCardCongr, PascalGridIdeal.boundarySlotReversal,
    allocatedPascalSlotReversal, Equiv.subtypeEquiv_apply, Equiv.finsetCongr_apply,
    Finset.mem_map, Equiv.toEmbedding_apply, Fin.revPerm_apply]
  constructor
  · rintro ⟨slot, ⟨source, hsource, rfl⟩, hcast⟩
    refine ⟨Fin.cast hsize source, ⟨source, hsource, rfl⟩, ?_⟩
    change Fin.cast hsize source.rev = index at hcast
    rw [Fin.cast_rev] at hcast
    exact hcast
  · rintro ⟨castSlot, ⟨source, hsource, rfl⟩, hrev⟩
    refine ⟨source.rev, ⟨source, hsource, rfl⟩, ?_⟩
    change Fin.cast hsize source.rev = index
    change (Fin.cast hsize source).rev = index at hrev
    rwa [Fin.cast_rev]

/-- Reflect all transition candidates precisely when the span's left endpoint
lies in the upper child of its allocated split. -/
def allocatedReflectedEndpointRankTransitionCandidates
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank}) :
    Finset (PascalGridIdeal (rank - 1) (k - rank - 1)) :=
  let profiles := allocatedEndpointRankTransitionProfiles
    chi lower upper color hrank hrankTop
  let candidates := allocatedEndpointTransitionCandidates profiles span
  if span.1.left ∈ lower then candidates
  else candidates.map
    (PascalGridIdeal.reflectedComplementEquiv
      (rank - 1) (k - rank - 1)).toEmbedding

/-- One reflected endpoint lane, normalized by the same orientation rule as
the complete candidate family. -/
def allocatedReflectedEndpointRankTransitionLane
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank})
    (side : SweepEndpointSide) :
    Finset (PascalGridIdeal (rank - 1) (k - rank - 1)) :=
  let profiles := allocatedEndpointRankTransitionProfiles
    chi lower upper color hrank hrankTop
  let lane := allocatedEndpointTransitionLane profiles span side
  if span.1.left ∈ lower then lane
  else lane.map
    (PascalGridIdeal.reflectedComplementEquiv
      (rank - 1) (k - rank - 1)).toEmbedding

/-- The normalized candidate family is still exactly the union of its two
normalized endpoint lanes. -/
theorem allocatedReflectedEndpointRankTransitionCandidates_eq_union_lanes
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank}) :
    allocatedReflectedEndpointRankTransitionCandidates
        chi lower upper color hrank hrankTop span =
      allocatedReflectedEndpointRankTransitionLane
          chi lower upper color hrank hrankTop span .left ∪
        allocatedReflectedEndpointRankTransitionLane
          chi lower upper color hrank hrankTop span .right := by
  classical
  by_cases hleft : span.1.left ∈ lower
  · simp [allocatedReflectedEndpointRankTransitionCandidates,
      allocatedReflectedEndpointRankTransitionLane, hleft,
      allocatedEndpointTransitionCandidates_eq_union_lanes]
  · simp [allocatedReflectedEndpointRankTransitionCandidates,
      allocatedReflectedEndpointRankTransitionLane, hleft,
      allocatedEndpointTransitionCandidates_eq_union_lanes, Finset.map_union]

/-- Reflection preserves nonemptiness of each individual endpoint lane. -/
theorem allocatedReflectedEndpointRankTransitionLane_nonempty
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank})
    (side : SweepEndpointSide) :
    (allocatedReflectedEndpointRankTransitionLane
      chi lower upper color hrank hrankTop span side).Nonempty := by
  classical
  let profiles := allocatedEndpointRankTransitionProfiles
    chi lower upper color hrank hrankTop
  have hnonempty := allocatedEndpointTransitionLane_nonempty profiles span side
  by_cases hleft : span.1.left ∈ lower
  · simpa [allocatedReflectedEndpointRankTransitionLane, profiles, hleft]
      using hnonempty
  · obtain ⟨ideal, hideal⟩ := hnonempty
    refine ⟨PascalGridIdeal.reflectedComplement ideal, ?_⟩
    simp only [allocatedReflectedEndpointRankTransitionLane, hleft,
      ↓reduceIte, Finset.mem_map, Equiv.toEmbedding_apply]
    exact ⟨ideal, hideal, rfl⟩

/-- Each normalized endpoint lane is contained in the complete normalized
candidate family. -/
theorem allocatedReflectedEndpointRankTransitionLane_subset_candidates
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank})
    (side : SweepEndpointSide) :
    allocatedReflectedEndpointRankTransitionLane
        chi lower upper color hrank hrankTop span side ⊆
      allocatedReflectedEndpointRankTransitionCandidates
        chi lower upper color hrank hrankTop span := by
  rw [allocatedReflectedEndpointRankTransitionCandidates_eq_union_lanes]
  cases side with
  | left => exact Finset.subset_union_left
  | right => exact Finset.subset_union_right

/-- Reflection preserves nonemptiness of every genuine endpoint-transition
candidate family.  This rules out the empty-family closed-star obstruction
before any expansion argument. -/
theorem allocatedReflectedEndpointRankTransitionCandidates_nonempty
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank}) :
    (allocatedReflectedEndpointRankTransitionCandidates
      chi lower upper color hrank hrankTop span).Nonempty := by
  classical
  let profiles := allocatedEndpointRankTransitionProfiles
    chi lower upper color hrank hrankTop
  have hnonempty :
      (allocatedEndpointTransitionCandidates profiles span).Nonempty :=
    allocatedEndpointTransitionCandidates_nonempty profiles span
  by_cases hleft : span.1.left ∈ lower
  · simpa [allocatedReflectedEndpointRankTransitionCandidates, profiles,
      hleft] using hnonempty
  · obtain ⟨candidate, hcandidate⟩ := hnonempty
    refine ⟨PascalGridIdeal.reflectedComplement candidate, ?_⟩
    rw [allocatedReflectedEndpointRankTransitionCandidates]
    simp only [hleft, ↓reduceIte, Finset.mem_map, Equiv.toEmbedding_apply]
    exact ⟨candidate, hcandidate, rfl⟩

/-- Full Hall expansion after orientation-normalizing candidate ideals. -/
def AllocatedReflectedEndpointRankTransitionHall
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k) : Prop :=
  ∀ spans : Finset {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank},
    spans.card ≤
      (spans.biUnion (allocatedReflectedEndpointRankTransitionCandidates
        chi lower upper color hrank hrankTop)).card

/-- Reflected Hall still constructs a slot injection into the unchanged
adjacent Pascal layer. -/
noncomputable def AllocatedExactRankSlotting.of_reflectedEndpointRankHall
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (hhall : AllocatedReflectedEndpointRankTransitionHall
      chi lower upper color hrank hrankTop) :
    AllocatedExactRankSlotting chi lower upper color rank k := by
  let matching := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (allocatedReflectedEndpointRankTransitionCandidates
      chi lower upper color hrank hrankTop)).mp hhall
  let representative := Classical.choose matching
  have hinjective : Function.Injective representative :=
    (Classical.choose_spec matching).1
  exact {
    slot := fun span ↦ PascalGridIdeal.rankIdealSlotEmbedding
      hrank hrankTop (representative span)
    injective := (PascalGridIdeal.rankIdealSlotEmbedding
      hrank hrankTop).injective.comp hinjective
  }

/-- The reflected Hall condition gives exactly the original local Pascal
capacity bound. -/
theorem allocatedExactRankFrontier_card_le_spanPascalDemand_of_reflectedHall
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (hhall : AllocatedReflectedEndpointRankTransitionHall
      chi lower upper color hrank hrankTop) :
    (allocatedExactRankFrontier chi lower upper color rank).card ≤
      publishedSpanPascalDemand k rank :=
  allocatedExactRankFrontier_card_le_spanPascalDemand_of_slotting
    (AllocatedExactRankSlotting.of_reflectedEndpointRankHall
      hrank hrankTop hhall)

end

end ErdosSzekeres

end
