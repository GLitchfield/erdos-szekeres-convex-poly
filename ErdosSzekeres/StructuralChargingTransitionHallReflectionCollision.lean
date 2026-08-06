module

public import ErdosSzekeres.StructuralChargingTransitionHallBlocks
public import ErdosSzekeres.StructuralChargingTransitionHallCollision

@[expose] public section

/-!
# The reflected encoding separates the frozen rigid collision

The two rigid full-ideal spans in the `n = 12`, `k = 7` counterexample cross
their allocated root in opposite orientations.  The reflected candidate
system leaves the first full ideal unchanged and sends the second to the empty
ideal, so this formerly Hall-deficient pair now expands to two states.
-/

namespace ErdosSzekeres
namespace StructuralChargingTransitionHallCollision

open StructuralChargingTransitionHallCollisionData

/-- The empty `2 x 3` ideal. -/
def emptyIdeal : PascalGridIdeal 2 3 where
  cells := ∅
  isLowerSet := by
    intro _ _ _ hmem
    simp at hmem

theorem reflectedComplement_fullIdeal :
    PascalGridIdeal.reflectedComplement fullIdeal = emptyIdeal := by
  ext cell
  simp [PascalGridIdeal.reflectedComplement, fullIdeal, emptyIdeal]

theorem first_reflectedCandidates :
    allocatedReflectedEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7) first =
        {fullIdeal} := by
  have hcandidates :
      allocatedEndpointTransitionCandidates profiles first = {fullIdeal} :=
    (allocatedEndpointTransitionCandidates_eq_singleton_iff
      profiles first fullIdeal).mpr first_rigid
  simpa [allocatedReflectedEndpointRankTransitionCandidates, profiles] using hcandidates

theorem second_reflectedCandidates :
    allocatedReflectedEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7) second =
        {emptyIdeal} := by
  have hcandidates :
      allocatedEndpointTransitionCandidates profiles second = {fullIdeal} :=
    (allocatedEndpointTransitionCandidates_eq_singleton_iff
      profiles second fullIdeal).mpr second_rigid
  simp only [allocatedReflectedEndpointRankTransitionCandidates, second]
  change (allocatedEndpointTransitionCandidates profiles second).map
      (PascalGridIdeal.reflectedComplementEquiv 2 3).toEmbedding = {emptyIdeal}
  rw [hcandidates]
  simp [PascalGridIdeal.reflectedComplementEquiv, reflectedComplement_fullIdeal]

/-- The reflected candidates repair the exact pair expansion that failed for
the unreflected endpoint profiles. -/
theorem reflectedPairExpansion :
    2 ≤ ((allocatedReflectedEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7) first) ∪
      (allocatedReflectedEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7) second)).card := by
  rw [first_reflectedCandidates, second_reflectedCandidates]
  decide

/-- The earlier member of the adjacent active-interval collision. -/
def blockFirstSpan : SweepSpanEndpoints 12 := ⟨2, 5⟩

theorem blockFirstSpan_exactRank :
    HasExactSpanRank .right color support blockFirstSpan 3 := by
  constructor
  · change HasCapSpanRankAtLeast color support 2 5 3
    refine ⟨{2, 3, 5}, by decide, by decide,
      isCapSet_of_turnSetBool (by decide), ?_⟩
    exact hasSweepSpan_of_subset_Icc (by decide) (by decide) (by decide) (by decide)
  · change ¬HasCapSpanRankAtLeast color support 2 5 4
    rintro ⟨chain, _, hcard, hcap, hspan⟩
    have hbound := sweepSpan_card_le_interval hspan
    have hsub : chain ⊆ Finset.Icc (2 : Fin 12) 5 := by
      intro x hx
      exact Finset.mem_Icc.mpr
        ⟨hspan.left_endpoint x hx, hspan.right_endpoint x hx⟩
    have heq : chain = Finset.Icc (2 : Fin 12) 5 := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [Fin.card_Icc]
      omega
    have hcolor := hcap ⟨2, 4, 5, by decide, by decide⟩
      (by rw [heq]; decide) (by rw [heq]; decide) (by rw [heq]; decide)
    have hleft : color ⟨2, 4, 5, by decide, by decide⟩ = .left := by decide
    rw [hleft] at hcolor
    contradiction

theorem blockFirstSpan_mem :
    blockFirstSpan ∈
      allocatedExactRankFrontier color lower upper .right 3 := by
  rw [mem_allocatedExactRankFrontier]
  constructor
  · rw [mem_allocatedExactRankSpans]
    exact ⟨⟨by decide, Or.inl ⟨by decide, by decide⟩⟩,
      by simpa [support] using blockFirstSpan_exactRank⟩
  · intro other hother hcontains
    have hcross := (mem_allocatedExactRankSpans.mp hother).1
    have hexact := (mem_allocatedExactRankSpans.mp hother).2
    rcases hexact.1 with ⟨chain, _, hcard, _, hchainSpan⟩
    have hbound := sweepSpan_card_le_interval hchainSpan
    change (2 : Fin 12) ≤ other.left ∧ other.right ≤ (5 : Fin 12) at hcontains
    have hleftVal : 2 ≤ other.left.val := hcontains.1
    have hrightVal : other.right.val ≤ 5 := hcontains.2
    have hwidth : 3 ≤ other.right.val + 1 - other.left.val :=
      hcard.trans hbound
    have hleftCases : other.left.val = 2 ∨ other.left.val = 3 := by omega
    have hrightCases : other.right.val = 4 ∨ other.right.val = 5 := by omega
    simp only [SweepSpanEndpoints.CrossesSplit] at hcross
    rcases hleftCases with hleft | hleft <;>
      rcases hrightCases with hright | hright
    · have hl : other.left = (2 : Fin 12) := Fin.ext hleft
      have hr : other.right = (4 : Fin 12) := Fin.ext hright
      rw [hl, hr] at hcross
      simp [lower, upper, lowerTree, upperTree,
        RankProfileCollision.DecompositionTree.vertices] at hcross
    · cases other with
      | mk left right =>
        simp only at hleft hright ⊢
        congr
        · exact Fin.ext hleft
        · exact Fin.ext hright
    · omega
    · have hl : other.left = (3 : Fin 12) := Fin.ext hleft
      have hr : other.right = (5 : Fin 12) := Fin.ext hright
      rw [hl, hr] at hcross
      simp [lower, upper, lowerTree, upperTree,
        RankProfileCollision.DecompositionTree.vertices] at hcross

def blockFirst : {span // span ∈
    allocatedExactRankFrontier color lower upper .right 3} :=
  ⟨blockFirstSpan, blockFirstSpan_mem⟩

/-- No retained span lies strictly between the two colliding active intervals. -/
theorem blockFirst_first_block :
    allocatedExactRankFrontierBlock blockFirst first = {blockFirst, first} := by
  ext span
  rw [mem_allocatedExactRankFrontierBlock]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hblock
    have hrightBlock : blockFirst.1.right ≤ span.1.right ∧
        span.1.right ≤ first.1.right := ⟨
      allocatedExactRankFrontier_left_le_iff_right_le.mp hblock.1,
      allocatedExactRankFrontier_left_le_iff_right_le.mp hblock.2⟩
    have hleftVal : 2 ≤ span.1.left.val := hblock.1
    have hrightLeftVal : span.1.left.val ≤ 4 := hblock.2
    have hleftCases : span.1.left.val = 2 ∨ span.1.left.val = 3 ∨
        span.1.left.val = 4 := by omega
    rcases hleftCases with hleft | hleft | hleft
    · left
      apply Subtype.ext
      apply allocatedExactRankFrontier_left_injective span.2 blockFirst.2
      exact Fin.ext hleft
    · have hrightLow : 5 ≤ span.1.right.val := hrightBlock.1
      have hrightHigh : span.1.right.val ≤ 6 := hrightBlock.2
      have hrightCases : span.1.right.val = 5 ∨
          span.1.right.val = 6 := by omega
      have hcross := (mem_allocatedExactRankFrontier.mp span.2).1
      have hcross := (mem_allocatedExactRankSpans.mp hcross).1
      simp only [SweepSpanEndpoints.CrossesSplit] at hcross
      rcases hrightCases with hright | hright
      · have hl : span.1.left = (3 : Fin 12) := Fin.ext hleft
        have hr : span.1.right = (5 : Fin 12) := Fin.ext hright
        rw [hl, hr] at hcross
        simp [lower, upper, lowerTree, upperTree,
          RankProfileCollision.DecompositionTree.vertices] at hcross
      · have hl : span.1.left = (3 : Fin 12) := Fin.ext hleft
        have hr : span.1.right = (6 : Fin 12) := Fin.ext hright
        rw [hl, hr] at hcross
        simp [lower, upper, lowerTree, upperTree,
          RankProfileCollision.DecompositionTree.vertices] at hcross
    · right
      apply Subtype.ext
      apply allocatedExactRankFrontier_left_injective span.2 first.2
      exact Fin.ext hleft
  · rintro (rfl | rfl)
    · exact ⟨le_rfl, by decide⟩
    · exact ⟨by decide, le_rfl⟩

theorem blockFirst_activeCandidates :
    allocatedReflectedActiveEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7)
        blockFirst = {fullIdeal} := by
  have hpast : profiles.past (5 : Fin 12) = fullIdeal := second_rigid.1
  have hfuture : profiles.future (5 : Fin 12) = fullIdeal := second_rigid.2.1
  have hinterval :
      allocatedActiveEndpointRankTransitionCandidates profiles blockFirst =
        {fullIdeal} := by
    rw [allocatedActiveEndpointRankTransitionCandidates]
    simp only [blockFirst, blockFirstSpan]
    rw [if_neg]
    · exact pascalTransitionInterval_eq_singleton_iff.mpr ⟨hpast, hfuture⟩
    · simp [lower, lowerTree, RankProfileCollision.DecompositionTree.vertices]
  simpa [allocatedReflectedActiveEndpointRankTransitionCandidates, profiles,
    blockFirst, blockFirstSpan, lower, lowerTree,
    RankProfileCollision.DecompositionTree.vertices] using hinterval

theorem first_activeCandidates :
    allocatedReflectedActiveEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7)
        first = {fullIdeal} := by
  have hpast : profiles.past (6 : Fin 12) = fullIdeal := first_rigid.2.2.1
  have hfuture : profiles.future (6 : Fin 12) = fullIdeal := first_rigid.2.2.2
  have hinterval :
      allocatedActiveEndpointRankTransitionCandidates profiles first =
        {fullIdeal} := by
    rw [allocatedActiveEndpointRankTransitionCandidates]
    simp only [first, firstSpan]
    rw [if_neg]
    · exact pascalTransitionInterval_eq_singleton_iff.mpr ⟨hpast, hfuture⟩
    · simp [lower, lowerTree, RankProfileCollision.DecompositionTree.vertices]
  simpa [allocatedReflectedActiveEndpointRankTransitionCandidates, profiles,
    first, firstSpan, lower, lowerTree,
    RankProfileCollision.DecompositionTree.vertices] using hinterval

theorem blockFirst_ne_first : blockFirst ≠ first := by decide

/-- Even the whole reflected interval at the active endpoint fails expansion
on this adjacent two-span block. -/
theorem activeBlockExpansion_fails :
    ¬AllocatedReflectedActiveEndpointRankTransitionBlockExpansion
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7) := by
  intro hexpansion
  have hbound := hexpansion blockFirst first
  rw [blockFirst_first_block] at hbound
  simp [blockFirst_ne_first, blockFirst_activeCandidates,
    first_activeCandidates] at hbound

end StructuralChargingTransitionHallCollision
end ErdosSzekeres

end
