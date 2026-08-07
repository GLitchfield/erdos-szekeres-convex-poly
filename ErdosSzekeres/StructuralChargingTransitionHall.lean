module

public import ErdosSzekeres.StructuralChargingSpanFrontier
public import Mathlib.Combinatorics.Hall.Basic

@[expose] public section

/-!
# Endpoint transition ideals and the local Hall target

Past and future cup--cap rank pairs at a sweep endpoint form lower ideals in a
finite rectangle. Such ideals inject into the adjacent Pascal layer through
the horizontal steps of their boundary paths. For each allocated exact-rank
span, this file allows any ideal between the past and future labels at either
endpoint.

Hall's condition for these two endpoint intervals is sufficient to construct
the exact slotting required by `StructuralChargingSpanFrontier`. The generic
ideal encoding and Hall bridge are proved here. Establishing Hall's condition
from deep-below incidence is the remaining geometry-specific theorem.
-/

namespace ErdosSzekeres

noncomputable section

/-- A lower ideal in a finite rectangular rank grid. -/
@[ext]
structure PascalGridIdeal (rows columns : ℕ) where
  cells : Finset (Fin rows × Fin columns)
  isLowerSet : IsLowerSet (cells : Set (Fin rows × Fin columns))

namespace PascalGridIdeal

theorem cells_injective {rows columns : ℕ} :
    Function.Injective (@PascalGridIdeal.cells rows columns) := by
  intro first second h
  exact PascalGridIdeal.ext h

instance {rows columns : ℕ} : SetLike (PascalGridIdeal rows columns)
    (Fin rows × Fin columns) where
  coe ideal := ideal.cells
  coe_injective' first second h := by
    rw [PascalGridIdeal.ext_iff, ← Finset.coe_inj]
    exact h

instance {rows columns : ℕ} : PartialOrder (PascalGridIdeal rows columns) :=
  PartialOrder.lift (fun ideal ↦ ideal.cells) PascalGridIdeal.cells_injective

instance {rows columns : ℕ} : DecidableEq (PascalGridIdeal rows columns) :=
  fun first second ↦ decidable_of_iff (first.cells = second.cells)
    PascalGridIdeal.ext_iff.symm

instance {rows columns : ℕ} : DecidableLE (PascalGridIdeal rows columns) :=
  fun first second ↦ inferInstanceAs (Decidable (first.cells ⊆ second.cells))

instance {rows columns : ℕ} : Max (PascalGridIdeal rows columns) where
  max first second := {
    cells := first.cells ∪ second.cells
    isLowerSet := by
      rw [Finset.coe_union]
      exact first.isLowerSet.union second.isLowerSet
  }

instance {rows columns : ℕ} : Min (PascalGridIdeal rows columns) where
  min first second := {
    cells := first.cells ∩ second.cells
    isLowerSet := by
      rw [Finset.coe_inter]
      exact first.isLowerSet.inter second.isLowerSet
  }

instance {rows columns : ℕ} : DistribLattice (PascalGridIdeal rows columns) :=
  Function.Injective.distribLattice PascalGridIdeal.cells
    PascalGridIdeal.cells_injective .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance {rows columns : ℕ} : Finite (PascalGridIdeal rows columns) :=
  Finite.of_injective PascalGridIdeal.cells PascalGridIdeal.cells_injective

noncomputable instance {rows columns : ℕ} : Fintype (PascalGridIdeal rows columns) :=
  Fintype.ofFinite _

/-- The cells in one row of a rectangular ideal. -/
def row {rows columns : ℕ} (ideal : PascalGridIdeal rows columns)
    (i : Fin rows) : Finset (Fin columns) :=
  Finset.univ.filter fun j ↦ (i, j) ∈ ideal.cells

@[simp] theorem mem_row {rows columns : ℕ}
    {ideal : PascalGridIdeal rows columns} {i : Fin rows} {j : Fin columns} :
    j ∈ ideal.row i ↔ (i, j) ∈ ideal.cells := by
  simp [row]

/-- The number of cells in one row. -/
def rowLength {rows columns : ℕ} (ideal : PascalGridIdeal rows columns)
    (i : Fin rows) : ℕ :=
  (ideal.row i).card

theorem mem_row_iff_lt_rowLength {rows columns : ℕ}
    {ideal : PascalGridIdeal rows columns} {i : Fin rows} {j : Fin columns} :
    j ∈ ideal.row i ↔ j.val < ideal.rowLength i := by
  constructor
  · intro hj
    have hsubset : Finset.Iic j ⊆ ideal.row i := by
      intro x hx
      rw [Finset.mem_Iic] at hx
      rw [mem_row] at hj ⊢
      exact ideal.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, hx⟩) hj
    have hcard := Finset.card_le_card hsubset
    rw [Fin.card_Iic] at hcard
    simpa [rowLength] using hcard
  · intro hlt
    by_contra hj
    have hsubset : ideal.row i ⊆ Finset.Iio j := by
      intro x hx
      rw [Finset.mem_Iio]
      by_contra hnot
      have hjx : j ≤ x := by omega
      apply hj
      rw [mem_row] at hx ⊢
      exact ideal.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, hjx⟩) hx
    have hcard := Finset.card_le_card hsubset
    rw [Fin.card_Iio] at hcard
    exact (not_lt_of_ge (by simpa [rowLength] using hcard)) hlt

theorem rowLength_le {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) (i : Fin rows) :
    ideal.rowLength i ≤ columns := by
  simpa [rowLength] using Finset.card_le_univ (ideal.row i)

theorem rowLength_anti {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) : Antitone ideal.rowLength := by
  intro first second hfirstSecond
  apply Finset.card_le_card
  intro j hj
  rw [mem_row] at hj ⊢
  exact ideal.isLowerSet (Prod.mk_le_mk.mpr ⟨hfirstSecond, le_rfl⟩) hj

theorem eq_of_rowLength_eq {rows columns : ℕ}
    {first second : PascalGridIdeal rows columns}
    (hrows : first.rowLength = second.rowLength) : first = second := by
  ext cell
  rw [← mem_row (ideal := first), ← mem_row (ideal := second),
    mem_row_iff_lt_rowLength, mem_row_iff_lt_rowLength, hrows]

/-- The horizontal-step index of one row on the boundary path of an ideal. -/
def boundaryIndex {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) (i : Fin rows) : Fin (rows + columns) :=
  ⟨i.val + (columns - ideal.rowLength i), by
    have hrow := ideal.rowLength_le i
    have hi := i.isLt
    omega⟩

theorem boundaryIndex_strictMono {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) : StrictMono ideal.boundaryIndex := by
  intro first second hfirstSecond
  change first.val + (columns - ideal.rowLength first) <
    second.val + (columns - ideal.rowLength second)
  have hlength := ideal.rowLength_anti (Fin.le_of_lt hfirstSecond)
  have hfirst := ideal.rowLength_le first
  have hsecond := ideal.rowLength_le second
  have hindices : first.val < second.val := hfirstSecond
  omega

/-- The boundary path as an order embedding of its horizontal steps. -/
def boundaryEmbedding {rows columns : ℕ}
    (ideal : PascalGridIdeal rows columns) : Fin rows ↪o Fin (rows + columns) :=
  OrderEmbedding.ofStrictMono ideal.boundaryIndex ideal.boundaryIndex_strictMono

/-- Encode an ideal by the `rows` horizontal-step positions of its boundary
path. -/
def boundarySlot {rows columns : ℕ} (ideal : PascalGridIdeal rows columns) :
    {indices : Finset (Fin (rows + columns)) // indices.card = rows} :=
  ⟨Finset.univ.map ideal.boundaryEmbedding.toEmbedding, by simp⟩

theorem boundarySlot_injective {rows columns : ℕ} :
    Function.Injective (@boundarySlot rows columns) := by
  intro first second hslots
  have hfinsets : Finset.univ.map first.boundaryEmbedding.toEmbedding =
      Finset.univ.map second.boundaryEmbedding.toEmbedding :=
    congrArg Subtype.val hslots
  have hranges : Set.range first.boundaryEmbedding =
      Set.range second.boundaryEmbedding := by
    ext x
    have hmem := Finset.ext_iff.mp hfinsets x
    simpa only [Finset.mem_map, Finset.mem_univ, true_and,
      EmbeddingLike.apply_eq_iff_eq, exists_eq_right] using hmem
  have hembeddings : first.boundaryEmbedding = second.boundaryEmbedding :=
    OrderEmbedding.range_eq_iff.mp hranges
  apply eq_of_rowLength_eq
  funext i
  have hindex := DFunLike.congr_fun hembeddings i
  have hindexVal := congrArg Fin.val hindex
  change i.val + (columns - first.rowLength i) =
    i.val + (columns - second.rowLength i) at hindexVal
  have hfirst := first.rowLength_le i
  have hsecond := second.rowLength_le i
  omega

/-- All rectangular ideals inject into one layer of Pascal's triangle. -/
def boundarySlotEmbedding (rows columns : ℕ) :
    PascalGridIdeal rows columns ↪
      {indices : Finset (Fin (rows + columns)) // indices.card = rows} :=
  ⟨boundarySlot, boundarySlot_injective⟩

/-- Transport fixed-cardinality slots across an equality of ambient sizes. -/
def finsetCardCongr {firstSize secondSize card : ℕ}
    (hsize : firstSize = secondSize) :
    {indices : Finset (Fin firstSize) // indices.card = card} ≃
      {indices : Finset (Fin secondSize) // indices.card = card} :=
  Equiv.subtypeEquiv
    (Equiv.finsetCongr (Fin.castOrderIso hsize).toEquiv) (by
      intro indices
      simp)

theorem rankRectangle_add_eq {rank k : ℕ}
    (hrank : 1 ≤ rank) (hrankTop : rank < k) :
    rank - 1 + (k - rank - 1) = k - 2 := by
  omega

/-- Boundary encoding specialized to the exact adjacent Pascal layer. -/
def rankIdealSlotEmbedding {rank k : ℕ}
    (hrank : 1 ≤ rank) (hrankTop : rank < k) :
    PascalGridIdeal (rank - 1) (k - rank - 1) ↪
      {indices : Finset (Fin (k - 2)) // indices.card = rank - 1} :=
  (boundarySlotEmbedding (rank - 1) (k - rank - 1)).trans
    (finsetCardCongr (rankRectangle_add_eq hrank hrankTop)).toEmbedding

end PascalGridIdeal

/-- The color complementary to a cup or cap rank. -/
def Turn.complement : Turn → Turn
  | .left => .right
  | .right => .left

@[simp] theorem Turn.complement_left : Turn.left.complement = Turn.right := rfl

@[simp] theorem Turn.complement_right : Turn.right.complement = Turn.left := rfl

@[simp] theorem Turn.complement_complement (color : Turn) :
    color.complement.complement = color := by
  cases color <;> rfl

/-- Lowering the requested threshold preserves a color-uniform span rank. -/
theorem HasSpanRankAtLeast.anti_rank {n : ℕ} {color : Turn}
    {chi : TripleColoring n} {s : Finset (Fin n)}
    {span : SweepSpanEndpoints n} {dominantRank dominatedRank : ℕ}
    (hspan : HasSpanRankAtLeast color chi s span dominantRank)
    (hrank : dominatedRank ≤ dominantRank) :
    HasSpanRankAtLeast color chi s span dominatedRank := by
  cases color with
  | left => exact HasCupSpanRankAtLeast.anti_rank hspan hrank
  | right => exact HasCapSpanRankAtLeast.anti_rank hspan hrank

/-- Rank pairs witnessed by spans ending before an endpoint form a finite
rectangular lower ideal. Coordinates zero and zero represent rank two. -/
def endpointPastRankIdeal {n : ℕ} (chi : TripleColoring n)
    (s : Finset (Fin n)) (color : Turn) (rank k : ℕ) (q : Fin n) :
    PascalGridIdeal (rank - 1) (k - rank - 1) where
  cells := by
    classical
    exact Finset.univ.filter fun cell ↦
      ∃ p ∈ s, p < q ∧
        HasSpanRankAtLeast color chi s ⟨p, q⟩ (cell.1.val + 2) ∧
        HasSpanRankAtLeast color.complement chi s ⟨p, q⟩ (cell.2.val + 2)
  isLowerSet := by
    classical
    intro larger smaller hle hlarger
    obtain ⟨p, hp, hpq, hsame, hopposite⟩ :=
      (Finset.mem_filter.mp hlarger).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, p, hp, hpq,
      hsame.anti_rank ?_, hopposite.anti_rank ?_⟩
    · exact Nat.add_le_add_right hle.1 2
    · exact Nat.add_le_add_right hle.2 2

/-- Rank pairs witnessed by spans starting after an endpoint form the future
lower ideal. -/
def endpointFutureRankIdeal {n : ℕ} (chi : TripleColoring n)
    (s : Finset (Fin n)) (color : Turn) (rank k : ℕ) (q : Fin n) :
    PascalGridIdeal (rank - 1) (k - rank - 1) where
  cells := by
    classical
    exact Finset.univ.filter fun cell ↦
      ∃ p ∈ s, q < p ∧
        HasSpanRankAtLeast color chi s ⟨q, p⟩ (cell.1.val + 2) ∧
        HasSpanRankAtLeast color.complement chi s ⟨q, p⟩ (cell.2.val + 2)
  isLowerSet := by
    classical
    intro larger smaller hle hlarger
    obtain ⟨p, hp, hqp, hsame, hopposite⟩ :=
      (Finset.mem_filter.mp hlarger).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, p, hp, hqp,
      hsame.anti_rank ?_, hopposite.anti_rank ?_⟩
    · exact Nat.add_le_add_right hle.1 2
    · exact Nat.add_le_add_right hle.2 2

/-- The existing slot codomain, named for reuse in transition systems. -/
abbrev AllocatedPascalSlot (rank k : ℕ) :=
  {indices : Finset (Fin (k - 2)) // indices.card = rank - 1}

/-- All lattice states between two endpoint states. -/
def pascalTransitionInterval {Ideal : Type*} [Fintype Ideal]
    [DecidableEq Ideal] [PartialOrder Ideal] [DecidableLE Ideal] [Lattice Ideal]
    (first second : Ideal) : Finset Ideal :=
  Finset.univ.filter fun state ↦ first ⊓ second ≤ state ∧ state ≤ first ⊔ second

theorem pascalTransitionInterval_first_mem {Ideal : Type*} [Fintype Ideal]
    [DecidableEq Ideal] [Lattice Ideal] [DecidableLE Ideal]
    (first second : Ideal) :
    first ∈ pascalTransitionInterval first second := by
  rw [pascalTransitionInterval, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, inf_le_left, le_sup_left⟩

theorem pascalTransitionInterval_second_mem {Ideal : Type*} [Fintype Ideal]
    [DecidableEq Ideal] [Lattice Ideal] [DecidableLE Ideal]
    (first second : Ideal) :
    second ∈ pascalTransitionInterval first second := by
  rw [pascalTransitionInterval, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, inf_le_right, le_sup_right⟩

/-- A transition interval is a singleton exactly when its endpoints are that
same lattice state. -/
theorem pascalTransitionInterval_eq_singleton_iff
    {Ideal : Type*} [Fintype Ideal] [DecidableEq Ideal]
    [Lattice Ideal] [DecidableLE Ideal] {first second state : Ideal} :
    pascalTransitionInterval first second = {state} ↔
      first = state ∧ second = state := by
  constructor
  · intro hsingleton
    have hfirst := pascalTransitionInterval_first_mem first second
    have hsecond := pascalTransitionInterval_second_mem first second
    rw [hsingleton] at hfirst hsecond
    exact ⟨by simpa using hfirst, by simpa using hsecond⟩
  · rintro ⟨rfl, rfl⟩
    ext candidate
    simp only [pascalTransitionInterval, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton, inf_idem, sup_idem]
    exact ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ h ▸ ⟨le_rfl, le_rfl⟩⟩

/-- Two nonempty finite candidate sets expand to at least two states exactly
when they are not the same singleton. -/
theorem Finset.two_le_card_union_iff_not_common_singleton
    {α : Type*} [DecidableEq α] {first second : Finset α}
    (hfirst : first.Nonempty) (hsecond : second.Nonempty) :
    2 ≤ (first ∪ second).card ↔
      ¬∃ state, first = {state} ∧ second = {state} := by
  constructor
  · intro hcard
    rintro ⟨state, rfl, rfl⟩
    simp at hcard
  · intro hnot
    by_contra hcard
    have hle : (first ∪ second).card ≤ 1 := by omega
    have hunionNonempty : (first ∪ second).Nonempty :=
      hfirst.mono Finset.subset_union_left
    have heq : (first ∪ second).card = 1 := by
      have hpos := Finset.card_pos.mpr hunionNonempty
      omega
    obtain ⟨state, hunion⟩ := Finset.card_eq_one.mp heq
    apply hnot
    refine ⟨state, ?_, ?_⟩
    · apply Finset.Subset.antisymm
      · intro candidate hcandidate
        have : candidate ∈ first ∪ second :=
          Finset.mem_union_left second hcandidate
        rw [hunion] at this
        exact this
      · rw [Finset.singleton_subset_iff]
        obtain ⟨candidate, hcandidate⟩ := hfirst
        have hcandidateState : candidate ∈ ({state} : Finset α) := by
          rw [← hunion]
          exact Finset.mem_union_left second hcandidate
        simp only [Finset.mem_singleton] at hcandidateState
        exact hcandidateState ▸ hcandidate
    · apply Finset.Subset.antisymm
      · intro candidate hcandidate
        have : candidate ∈ first ∪ second :=
          Finset.mem_union_right first hcandidate
        rw [hunion] at this
        exact this
      · rw [Finset.singleton_subset_iff]
        obtain ⟨candidate, hcandidate⟩ := hsecond
        have hcandidateState : candidate ∈ ({state} : Finset α) := by
          rw [← hunion]
          exact Finset.mem_union_right first hcandidate
        simp only [Finset.mem_singleton] at hcandidateState
        exact hcandidateState ▸ hcandidate

/-- Past and future endpoint profiles, together with an encoding of all
profile states into the correct Pascal layer. -/
structure AllocatedEndpointTransitionProfiles {n : ℕ}
    (chi : TripleColoring n) (lower upper : Finset (Fin n))
    (color : Turn) (rank k : ℕ) (Ideal : Type*)
    [Fintype Ideal] [DecidableEq Ideal] where
  past : Fin n → Ideal
  future : Fin n → Ideal
  encode : Ideal ↪ AllocatedPascalSlot rank k

/-- The actual truncated same/opposite rank ideals attached to each sweep
endpoint. The omitted opposite threshold is `k + 1 - rank`; retaining it
would move to the next Pascal row rather than the required adjacent layer. -/
def allocatedEndpointRankTransitionProfiles {n rank k : ℕ}
    (chi : TripleColoring n) (lower upper : Finset (Fin n))
    (color : Turn) (hrank : 1 ≤ rank) (hrankTop : rank < k) :
    AllocatedEndpointTransitionProfiles chi lower upper color rank k
      (PascalGridIdeal (rank - 1) (k - rank - 1)) where
  past := endpointPastRankIdeal chi (lower ∪ upper) color rank k
  future := endpointFutureRankIdeal chi (lower ∪ upper) color rank k
  encode := PascalGridIdeal.rankIdealSlotEmbedding hrank hrankTop

/-- A span may use a transition state at either of its two endpoints. -/
def allocatedEndpointTransitionCandidates {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [PartialOrder Ideal] [Lattice Ideal]
    [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank}) : Finset Ideal :=
  pascalTransitionInterval (profiles.past span.1.left)
      (profiles.future span.1.left) ∪
    pascalTransitionInterval (profiles.past span.1.right)
      (profiles.future span.1.right)

/-- One of the two endpoint transition lanes before orientation
normalization. Their union is the complete candidate family above. -/
def allocatedEndpointTransitionLane {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [Lattice Ideal] [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank}) :
    SweepEndpointSide → Finset Ideal
  | .left =>
      pascalTransitionInterval (profiles.past span.1.left)
        (profiles.future span.1.left)
  | .right =>
      pascalTransitionInterval (profiles.past span.1.right)
        (profiles.future span.1.right)

/-- The complete endpoint-transition family is exactly the union of its two
endpoint lanes. -/
theorem allocatedEndpointTransitionCandidates_eq_union_lanes
    {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [Lattice Ideal] [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank}) :
    allocatedEndpointTransitionCandidates profiles span =
      allocatedEndpointTransitionLane profiles span .left ∪
        allocatedEndpointTransitionLane profiles span .right := by
  rfl

/-- Every endpoint lane is nonempty because it contains both interval
endpoints. -/
theorem allocatedEndpointTransitionLane_nonempty
    {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [Lattice Ideal] [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank})
    (side : SweepEndpointSide) :
    (allocatedEndpointTransitionLane profiles span side).Nonempty := by
  cases side with
  | left =>
      exact ⟨profiles.past span.1.left,
        pascalTransitionInterval_first_mem _ _⟩
  | right =>
      exact ⟨profiles.past span.1.right,
        pascalTransitionInterval_first_mem _ _⟩

/-- Either endpoint lane is contained in the complete two-lane family. -/
theorem allocatedEndpointTransitionLane_subset_candidates
    {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [Lattice Ideal] [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank})
    (side : SweepEndpointSide) :
    allocatedEndpointTransitionLane profiles span side ⊆
      allocatedEndpointTransitionCandidates profiles span := by
  rw [allocatedEndpointTransitionCandidates_eq_union_lanes]
  cases side with
  | left => exact Finset.subset_union_left
  | right => exact Finset.subset_union_right

/-- A finite family is a lattice chain interval when it is a complete
transition interval and all of its members are pairwise comparable. -/
def PascalGridIdeal.IsChainInterval {rows columns : ℕ}
    (anchors : Finset (PascalGridIdeal rows columns)) : Prop :=
  ∃ first ∈ anchors, ∃ second ∈ anchors,
    anchors = pascalTransitionInterval first second ∧
      ∀ ideal ∈ anchors, ∀ other ∈ anchors,
        ideal ≤ other ∨ other ≤ ideal

/-- The four past/future endpoint labels that generate a span's two transition
intervals. -/
def allocatedEndpointTransitionExtremes {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank}) : Finset Ideal :=
  {
    profiles.past span.1.left,
    profiles.future span.1.left,
    profiles.past span.1.right,
    profiles.future span.1.right
  }

/-- Every endpoint extreme belongs to the complete two-interval candidate
family it generates. -/
theorem allocatedEndpointTransitionExtremes_subset {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [Lattice Ideal] [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank}) :
    allocatedEndpointTransitionExtremes profiles span ⊆
      allocatedEndpointTransitionCandidates profiles span := by
  intro ideal hideal
  simp only [allocatedEndpointTransitionExtremes, Finset.mem_insert,
    Finset.mem_singleton] at hideal
  rcases hideal with rfl | rfl | rfl | rfl
  · rw [allocatedEndpointTransitionCandidates]
    exact Finset.mem_union_left _
      (pascalTransitionInterval_first_mem
        (profiles.past span.1.left) (profiles.future span.1.left))
  · rw [allocatedEndpointTransitionCandidates]
    exact Finset.mem_union_left _
      (pascalTransitionInterval_second_mem
        (profiles.past span.1.left) (profiles.future span.1.left))
  · rw [allocatedEndpointTransitionCandidates]
    exact Finset.mem_union_right _
      (pascalTransitionInterval_first_mem
        (profiles.past span.1.right) (profiles.future span.1.right))
  · rw [allocatedEndpointTransitionCandidates]
    exact Finset.mem_union_right _
      (pascalTransitionInterval_second_mem
        (profiles.past span.1.right) (profiles.future span.1.right))

theorem allocatedEndpointTransitionCandidates_nonempty
    {n : ℕ} {Ideal : Type*} [Fintype Ideal] [DecidableEq Ideal]
    [Lattice Ideal] [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank}) :
    (allocatedEndpointTransitionCandidates profiles span).Nonempty := by
  refine ⟨profiles.past span.1.left, ?_⟩
  rw [allocatedEndpointTransitionCandidates, Finset.mem_union]
  exact Or.inl (pascalTransitionInterval_first_mem _ _)

/-- A rigid span has the same past and future state at both endpoints. -/
def AllocatedEndpointTransitionRigidAt {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank})
    (state : Ideal) : Prop :=
  profiles.past span.1.left = state ∧
    profiles.future span.1.left = state ∧
    profiles.past span.1.right = state ∧
    profiles.future span.1.right = state

/-- A span has one available state exactly when all four endpoint labels are
that state. -/
theorem allocatedEndpointTransitionCandidates_eq_singleton_iff
    {n : ℕ} {Ideal : Type*} [Fintype Ideal] [DecidableEq Ideal]
    [Lattice Ideal] [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (span : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank})
    (state : Ideal) :
    allocatedEndpointTransitionCandidates profiles span = {state} ↔
      AllocatedEndpointTransitionRigidAt profiles span state := by
  constructor
  · intro hsingleton
    have hpastLeft :
        profiles.past span.1.left ∈
          allocatedEndpointTransitionCandidates profiles span := by
      rw [allocatedEndpointTransitionCandidates, Finset.mem_union]
      exact Or.inl (pascalTransitionInterval_first_mem _ _)
    have hfutureLeft :
        profiles.future span.1.left ∈
          allocatedEndpointTransitionCandidates profiles span := by
      rw [allocatedEndpointTransitionCandidates, Finset.mem_union]
      exact Or.inl (pascalTransitionInterval_second_mem _ _)
    have hpastRight :
        profiles.past span.1.right ∈
          allocatedEndpointTransitionCandidates profiles span := by
      rw [allocatedEndpointTransitionCandidates, Finset.mem_union]
      exact Or.inr (pascalTransitionInterval_first_mem _ _)
    have hfutureRight :
        profiles.future span.1.right ∈
          allocatedEndpointTransitionCandidates profiles span := by
      rw [allocatedEndpointTransitionCandidates, Finset.mem_union]
      exact Or.inr (pascalTransitionInterval_second_mem _ _)
    rw [hsingleton] at hpastLeft hfutureLeft hpastRight hfutureRight
    exact ⟨by simpa using hpastLeft, by simpa using hfutureLeft,
      by simpa using hpastRight, by simpa using hfutureRight⟩
  · rintro ⟨hpastLeft, hfutureLeft, hpastRight, hfutureRight⟩
    rw [allocatedEndpointTransitionCandidates,
      (pascalTransitionInterval_eq_singleton_iff.mpr
        ⟨hpastLeft, hfutureLeft⟩),
      (pascalTransitionInterval_eq_singleton_iff.mpr
        ⟨hpastRight, hfutureRight⟩), Finset.union_self]

/-- The size-two part of Hall expansion. -/
def AllocatedEndpointTransitionPairExpansion {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [Lattice Ideal] [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal) : Prop :=
  ∀ first second : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank},
    first ≠ second →
      2 ≤ (allocatedEndpointTransitionCandidates profiles first ∪
        allocatedEndpointTransitionCandidates profiles second).card

/-- Rigid endpoint labels identify at most one retained span. -/
def AllocatedEndpointTransitionRigidLabelInjective
    {n : ℕ} {Ideal : Type*} [Fintype Ideal] [DecidableEq Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal) : Prop :=
  ∀ first second : {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank},
    ∀ state,
      AllocatedEndpointTransitionRigidAt profiles first state →
      AllocatedEndpointTransitionRigidAt profiles second state →
      first = second

/-- The two-span Hall obstruction is exactly a collision between rigid spans,
not an arbitrary overlap of transition intervals. -/
theorem allocatedEndpointTransitionPairExpansion_iff_rigidLabelInjective
    {n : ℕ} {Ideal : Type*} [Fintype Ideal] [DecidableEq Ideal]
    [Lattice Ideal] [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal) :
    AllocatedEndpointTransitionPairExpansion profiles ↔
      AllocatedEndpointTransitionRigidLabelInjective profiles := by
  constructor
  · intro hexpansion first second state hfirst hsecond
    by_contra hne
    have hcard := hexpansion first second hne
    rw [(allocatedEndpointTransitionCandidates_eq_singleton_iff
      profiles first state).mpr hfirst,
      (allocatedEndpointTransitionCandidates_eq_singleton_iff
        profiles second state).mpr hsecond] at hcard
    simp at hcard
  · intro hinjective first second hne
    rw [Finset.two_le_card_union_iff_not_common_singleton
      (allocatedEndpointTransitionCandidates_nonempty profiles first)
      (allocatedEndpointTransitionCandidates_nonempty profiles second)]
    rintro ⟨state, hfirst, hsecond⟩
    apply hne
    exact hinjective first second state
      ((allocatedEndpointTransitionCandidates_eq_singleton_iff
        profiles first state).mp hfirst)
      ((allocatedEndpointTransitionCandidates_eq_singleton_iff
        profiles second state).mp hsecond)

/-- Hall's condition for the two-way endpoint transition intervals. -/
def AllocatedEndpointTransitionHall {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [PartialOrder Ideal] [Lattice Ideal]
    [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal) : Prop :=
  ∀ spans : Finset {span // span ∈
      allocatedExactRankFrontier chi lower upper color rank},
    spans.card ≤
      (spans.biUnion (allocatedEndpointTransitionCandidates profiles)).card

/-- Full Hall expansion contains the previously isolated two-span test. -/
theorem allocatedEndpointTransitionHall_implies_pairExpansion
    {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [Lattice Ideal]
    [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    {profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal}
    (hhall : AllocatedEndpointTransitionHall profiles) :
    AllocatedEndpointTransitionPairExpansion profiles := by
  intro first second hne
  simpa [hne] using hhall {first, second}

/-- The transition-interval Hall condition constructs the exact slotting
needed by the local Pascal bound. -/
noncomputable def AllocatedEndpointTransitionProfiles.toSlotting_of_hall
    {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [PartialOrder Ideal] [Lattice Ideal]
    [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (hhall : AllocatedEndpointTransitionHall profiles) :
    AllocatedExactRankSlotting chi lower upper color rank k := by
  let matching := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (allocatedEndpointTransitionCandidates profiles)).mp hhall
  let representative := Classical.choose matching
  have hinjective : Function.Injective representative :=
    (Classical.choose_spec matching).1
  exact {
    slot := fun span ↦ profiles.encode (representative span)
    injective := profiles.encode.injective.comp hinjective
  }

/-- The transition-interval Hall condition implies the local Pascal bound. -/
theorem allocatedExactRankFrontier_card_le_spanPascalDemand_of_transitionHall
    {n : ℕ} {Ideal : Type*}
    [Fintype Ideal] [DecidableEq Ideal] [PartialOrder Ideal] [Lattice Ideal]
    [DecidableLE Ideal]
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {rank k : ℕ}
    (profiles : AllocatedEndpointTransitionProfiles
      chi lower upper color rank k Ideal)
    (hhall : AllocatedEndpointTransitionHall profiles) :
    (allocatedExactRankFrontier chi lower upper color rank).card ≤
      publishedSpanPascalDemand k rank :=
  allocatedExactRankFrontier_card_le_spanPascalDemand_of_slotting
    (profiles.toSlotting_of_hall hhall)

/-- Concrete Hall expansion for the endpoint rank-transition ideals. This is
the geometry-specific statement supported by the bounded gates and left for a
structural proof. -/
def AllocatedEndpointRankTransitionHall {n rank k : ℕ}
    (chi : TripleColoring n) (lower upper : Finset (Fin n))
    (color : Turn) (hrank : 1 ≤ rank) (hrankTop : rank < k) : Prop :=
  AllocatedEndpointTransitionHall
    (allocatedEndpointRankTransitionProfiles
      chi lower upper color hrank hrankTop)

/-- The concrete endpoint-rank Hall condition yields the local Pascal demand
bound with no further combinatorial assumption. -/
theorem allocatedExactRankFrontier_card_le_spanPascalDemand_of_endpointRankHall
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (hhall : AllocatedEndpointRankTransitionHall
      chi lower upper color hrank hrankTop) :
    (allocatedExactRankFrontier chi lower upper color rank).card ≤
      publishedSpanPascalDemand k rank :=
  allocatedExactRankFrontier_card_le_spanPascalDemand_of_transitionHall
    (allocatedEndpointRankTransitionProfiles
      chi lower upper color hrank hrankTop) hhall

end

end ErdosSzekeres

end
