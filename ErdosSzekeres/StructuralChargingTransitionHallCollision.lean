module

public import ErdosSzekeres.StructuralChargingTransitionHallCollisionData
public import ErdosSzekeres.StructuralChargingTransitionHall

@[expose] public section

/-!
# A decomposable collision for endpoint-transition Hall

This file kernel-checks the rank-three collision found after the first bounded
transition-Hall gate.  At `n = 12` and `k = 7`, two distinct retained cap
spans have the same rigid full ideal.  Consequently both candidate sets are
the same singleton, refuting rigid-label injectivity and the proposed
all-parameter endpoint-transition Hall condition.
-/

namespace ErdosSzekeres
namespace StructuralChargingTransitionHallCollision

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open StructuralChargingTransitionHallCollisionData

/-- Executable checker for monochromaticity of all triples in a concrete set. -/
def turnSetBool (chi : TripleColoring 12) (s : Finset (Fin 12))
    (turn : Turn) : Bool :=
  (List.finRange 12).all fun i ↦
    (List.finRange 12).all fun j ↦
      (List.finRange 12).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              decide (chi ⟨i, j, k, hij, hjk⟩ = turn)
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (chi : TripleColoring 12)
    (s : Finset (Fin 12)) (turn : Turn) :
    turnSetBool chi s turn = true ↔
      ∀ t : OrderedTriple 12, t.i ∈ s → t.j ∈ s → t.k ∈ s →
        chi t = turn := by
  constructor
  · intro h t hi hj hk
    have hiCheck := (List.all_eq_true.mp h) t.i (List.mem_finRange t.i)
    have hjCheck := (List.all_eq_true.mp hiCheck) t.j (List.mem_finRange t.j)
    have hkCheck := (List.all_eq_true.mp hjCheck) t.k (List.mem_finRange t.k)
    simpa [turnSetBool, t.hij, t.hjk, hi, hj, hk] using hkCheck
  · intro h
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    apply List.all_eq_true.mpr
    intro k _
    by_cases hij : i < j
    · by_cases hjk : j < k
      · by_cases hi : i ∈ s
        · by_cases hj : j ∈ s
          · by_cases hk : k ∈ s
            · simp [hij, hjk, hi, hj, hk,
                h ⟨i, j, k, hij, hjk⟩ hi hj hk]
            · simp [hij, hjk, hi, hj, hk]
          · simp [hij, hjk, hi, hj]
        · simp [hij, hjk, hi]
      · simp [hij, hjk]
    · simp [hij]

theorem isCapSet_of_turnSetBool {s : Finset (Fin 12)}
    (h : turnSetBool color s .right = true) : IsCapSet color s := by
  simpa [IsCapSet] using (turnSetBool_eq_true_iff color s .right).mp h

theorem isCupSet_of_turnSetBool {s : Finset (Fin 12)}
    (h : turnSetBool color s .left = true) : IsCupSet color s := by
  simpa [IsCupSet] using (turnSetBool_eq_true_iff color s .left).mp h

theorem sweepSpan_card_le_interval {chain : Finset (Fin 12)} {a b : Fin 12}
    (hspan : HasSweepSpan chain a b) :
    chain.card ≤ b.val + 1 - a.val := by
  calc
    chain.card ≤ (Finset.Icc a b).card := by
      apply Finset.card_le_card
      intro x hx
      exact Finset.mem_Icc.mpr
        ⟨hspan.left_endpoint x hx, hspan.right_endpoint x hx⟩
    _ = b.val + 1 - a.val := Fin.card_Icc a b

theorem hasSweepSpan_of_subset_Icc {chain : Finset (Fin 12)} {a b : Fin 12}
    (hlt : a < b) (ha : a ∈ chain) (hb : b ∈ chain)
    (hsub : chain ⊆ Finset.Icc a b) : HasSweepSpan chain a b := by
  exact ⟨hlt, ha, hb,
    fun x hx ↦ (Finset.mem_Icc.mp (hsub hx)).1,
    fun x hx ↦ (Finset.mem_Icc.mp (hsub hx)).2⟩

def firstSpan : SweepSpanEndpoints 12 := ⟨4, 6⟩

def secondSpan : SweepSpanEndpoints 12 := ⟨5, 7⟩

theorem firstSpan_exactRank :
    HasExactSpanRank .right color support firstSpan 3 := by
  constructor
  · change HasCapSpanRankAtLeast color support 4 6 3
    refine ⟨{4, 5, 6}, by decide, by decide,
      isCapSet_of_turnSetBool (by decide), ?_⟩
    exact hasSweepSpan_of_subset_Icc (by decide) (by decide) (by decide) (by decide)
  · change ¬HasCapSpanRankAtLeast color support 4 6 4
    rintro ⟨chain, _, hcard, _, hspan⟩
    have hbound := sweepSpan_card_le_interval hspan
    omega

theorem secondSpan_exactRank :
    HasExactSpanRank .right color support secondSpan 3 := by
  constructor
  · change HasCapSpanRankAtLeast color support 5 7 3
    refine ⟨{5, 6, 7}, by decide, by decide,
      isCapSet_of_turnSetBool (by decide), ?_⟩
    exact hasSweepSpan_of_subset_Icc (by decide) (by decide) (by decide) (by decide)
  · change ¬HasCapSpanRankAtLeast color support 5 7 4
    rintro ⟨chain, _, hcard, _, hspan⟩
    have hbound := sweepSpan_card_le_interval hspan
    omega

theorem widthTwo_exactRankThree_mem_frontier
    (span : SweepSpanEndpoints 12)
    (hcross : span.CrossesSplit lower upper)
    (hexact : HasExactSpanRank .right color support span 3)
    (hwidth : span.right.val = span.left.val + 2) :
    span ∈ allocatedExactRankFrontier color lower upper .right 3 := by
  rw [mem_allocatedExactRankFrontier]
  constructor
  · rw [mem_allocatedExactRankSpans]
    simpa [support] using And.intro hcross hexact
  · intro other hother hcontains
    have hotherExact := (mem_allocatedExactRankSpans.mp hother).2
    change HasCapSpanRankAtLeast color (lower ∪ upper)
      other.left other.right 3 ∧ _ at hotherExact
    rcases hotherExact.1 with ⟨chain, _, hcard, _, hchainSpan⟩
    have hbound := sweepSpan_card_le_interval hchainSpan
    have hleft := hcontains.1
    have hright := hcontains.2
    have hleftVal : span.left.val ≤ other.left.val := hleft
    have hrightVal : other.right.val ≤ span.right.val := hright
    have hotherLeft : other.left.val = span.left.val := by omega
    have hotherRight : other.right.val = span.right.val := by omega
    cases span with
    | mk spanLeft spanRight =>
      cases other with
      | mk otherLeft otherRight =>
        simp only at hotherLeft hotherRight ⊢
        congr
        · exact Fin.ext hotherLeft
        · exact Fin.ext hotherRight

theorem firstSpan_mem :
    firstSpan ∈ allocatedExactRankFrontier color lower upper .right 3 := by
  apply widthTwo_exactRankThree_mem_frontier firstSpan
  · exact ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩
  · exact firstSpan_exactRank
  · decide

theorem secondSpan_mem :
    secondSpan ∈ allocatedExactRankFrontier color lower upper .right 3 := by
  apply widthTwo_exactRankThree_mem_frontier secondSpan
  · exact ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩
  · exact secondSpan_exactRank
  · decide

def first : {span // span ∈
    allocatedExactRankFrontier color lower upper .right 3} :=
  ⟨firstSpan, firstSpan_mem⟩

def second : {span // span ∈
    allocatedExactRankFrontier color lower upper .right 3} :=
  ⟨secondSpan, secondSpan_mem⟩

def fullIdeal : PascalGridIdeal 2 3 where
  cells := Finset.univ
  isLowerSet := by
    intro _ _ _ _
    simp

theorem capSpanRank_of_chain (chain : Finset (Fin 12)) (a b : Fin 12)
    (rank : ℕ) (hsub : chain ⊆ support) (hcard : rank ≤ chain.card)
    (hcap : turnSetBool color chain .right = true)
    (hlt : a < b) (ha : a ∈ chain) (hb : b ∈ chain)
    (hinterval : chain ⊆ Finset.Icc a b) :
    HasSpanRankAtLeast .right color support ⟨a, b⟩ rank := by
  exact ⟨chain, hsub, hcard, isCapSet_of_turnSetBool hcap,
    hasSweepSpan_of_subset_Icc hlt ha hb hinterval⟩

theorem cupSpanRank_of_chain (chain : Finset (Fin 12)) (a b : Fin 12)
    (rank : ℕ) (hsub : chain ⊆ support) (hcard : rank ≤ chain.card)
    (hcup : turnSetBool color chain .left = true)
    (hlt : a < b) (ha : a ∈ chain) (hb : b ∈ chain)
    (hinterval : chain ⊆ Finset.Icc a b) :
    HasSpanRankAtLeast .left color support ⟨a, b⟩ rank := by
  exact ⟨chain, hsub, hcard, isCupSet_of_turnSetBool hcup,
    hasSweepSpan_of_subset_Icc hlt ha hb hinterval⟩

theorem rankPair_zero_four :
    HasSpanRankAtLeast .right color support ⟨0, 4⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨0, 4⟩ 4 := by
  constructor
  · exact capSpanRank_of_chain {0, 3, 4} 0 4 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact cupSpanRank_of_chain {0, 1, 2, 4} 0 4 4
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem rankPair_four_eleven :
    HasSpanRankAtLeast .right color support ⟨4, 11⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨4, 11⟩ 4 := by
  constructor
  · exact capSpanRank_of_chain {4, 5, 11} 4 11 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact cupSpanRank_of_chain {4, 7, 10, 11} 4 11 4
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem rankPair_one_five :
    HasSpanRankAtLeast .right color support ⟨1, 5⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨1, 5⟩ 4 := by
  constructor
  · exact capSpanRank_of_chain {1, 3, 5} 1 5 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact cupSpanRank_of_chain {1, 2, 4, 5} 1 5 4
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem rankPair_five_ten :
    HasSpanRankAtLeast .right color support ⟨5, 10⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨5, 10⟩ 4 := by
  constructor
  · exact capSpanRank_of_chain {5, 6, 10} 5 10 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact cupSpanRank_of_chain {5, 7, 8, 10} 5 10 4
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem rankPair_zero_six :
    HasSpanRankAtLeast .right color support ⟨0, 6⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨0, 6⟩ 4 := by
  constructor
  · exact capSpanRank_of_chain {0, 5, 6} 0 6 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact cupSpanRank_of_chain {0, 1, 2, 6} 0 6 4
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem rankPair_six_ten :
    HasSpanRankAtLeast .right color support ⟨6, 10⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨6, 10⟩ 4 := by
  constructor
  · exact capSpanRank_of_chain {6, 9, 10} 6 10 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact cupSpanRank_of_chain {6, 7, 8, 10} 6 10 4
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem rankPair_zero_seven :
    HasSpanRankAtLeast .right color support ⟨0, 7⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨0, 7⟩ 4 := by
  constructor
  · exact capSpanRank_of_chain {0, 3, 7} 0 7 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact cupSpanRank_of_chain {0, 1, 2, 7} 0 7 4
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem rankPair_seven_eleven :
    HasSpanRankAtLeast .right color support ⟨7, 11⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨7, 11⟩ 4 := by
  constructor
  · exact capSpanRank_of_chain {7, 9, 11} 7 11 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact cupSpanRank_of_chain {7, 8, 10, 11} 7 11 4
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

def maxCell : Fin 2 × Fin 3 := (1, 2)

theorem ideal_eq_fullIdeal_of_maxCell_mem (ideal : PascalGridIdeal 2 3)
    (hmax : maxCell ∈ ideal) : ideal = fullIdeal := by
  apply PascalGridIdeal.ext
  apply Finset.eq_univ_iff_forall.mpr
  intro cell
  apply ideal.isLowerSet (a := maxCell)
  · exact ⟨Fin.le_last _, Fin.le_last _⟩
  · exact hmax

theorem endpointPast_eq_fullIdeal (p q : Fin 12) (hp : p ∈ support)
    (hpq : p < q)
    (hranks : HasSpanRankAtLeast .right color support ⟨p, q⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨p, q⟩ 4) :
    endpointPastRankIdeal color support .right 3 7 q = fullIdeal := by
  classical
  apply ideal_eq_fullIdeal_of_maxCell_mem
  change maxCell ∈ Finset.univ.filter fun cell ↦
    ∃ p ∈ support, p < q ∧
      HasSpanRankAtLeast .right color support ⟨p, q⟩ (cell.1.val + 2) ∧
      HasSpanRankAtLeast .left color support ⟨p, q⟩ (cell.2.val + 2)
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, p, hp, hpq, by simpa [maxCell] using hranks.1,
    by simpa [maxCell] using hranks.2⟩

theorem endpointFuture_eq_fullIdeal (q p : Fin 12) (hp : p ∈ support)
    (hqp : q < p)
    (hranks : HasSpanRankAtLeast .right color support ⟨q, p⟩ 3 ∧
      HasSpanRankAtLeast .left color support ⟨q, p⟩ 4) :
    endpointFutureRankIdeal color support .right 3 7 q = fullIdeal := by
  classical
  apply ideal_eq_fullIdeal_of_maxCell_mem
  change maxCell ∈ Finset.univ.filter fun cell ↦
    ∃ p ∈ support, q < p ∧
      HasSpanRankAtLeast .right color support ⟨q, p⟩ (cell.1.val + 2) ∧
      HasSpanRankAtLeast .left color support ⟨q, p⟩ (cell.2.val + 2)
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, p, hp, hqp, by simpa [maxCell] using hranks.1,
    by simpa [maxCell] using hranks.2⟩

noncomputable def profiles : AllocatedEndpointTransitionProfiles
    color lower upper .right 3 7 (PascalGridIdeal 2 3) :=
  allocatedEndpointRankTransitionProfiles color lower upper .right
    (by decide) (by decide)

theorem first_rigid :
    AllocatedEndpointTransitionRigidAt profiles first fullIdeal := by
  change
    endpointPastRankIdeal color (lower ∪ upper) .right 3 7 4 = fullIdeal ∧
    endpointFutureRankIdeal color (lower ∪ upper) .right 3 7 4 = fullIdeal ∧
    endpointPastRankIdeal color (lower ∪ upper) .right 3 7 6 = fullIdeal ∧
    endpointFutureRankIdeal color (lower ∪ upper) .right 3 7 6 = fullIdeal
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [support] using
      endpointPast_eq_fullIdeal 0 4 (by decide) (by decide) rankPair_zero_four
  · simpa [support] using
      endpointFuture_eq_fullIdeal 4 11 (by decide) (by decide) rankPair_four_eleven
  · simpa [support] using
      endpointPast_eq_fullIdeal 0 6 (by decide) (by decide) rankPair_zero_six
  · simpa [support] using
      endpointFuture_eq_fullIdeal 6 10 (by decide) (by decide) rankPair_six_ten

theorem second_rigid :
    AllocatedEndpointTransitionRigidAt profiles second fullIdeal := by
  change
    endpointPastRankIdeal color (lower ∪ upper) .right 3 7 5 = fullIdeal ∧
    endpointFutureRankIdeal color (lower ∪ upper) .right 3 7 5 = fullIdeal ∧
    endpointPastRankIdeal color (lower ∪ upper) .right 3 7 7 = fullIdeal ∧
    endpointFutureRankIdeal color (lower ∪ upper) .right 3 7 7 = fullIdeal
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [support] using
      endpointPast_eq_fullIdeal 1 5 (by decide) (by decide) rankPair_one_five
  · simpa [support] using
      endpointFuture_eq_fullIdeal 5 10 (by decide) (by decide) rankPair_five_ten
  · simpa [support] using
      endpointPast_eq_fullIdeal 0 7 (by decide) (by decide) rankPair_zero_seven
  · simpa [support] using
      endpointFuture_eq_fullIdeal 7 11 (by decide) (by decide) rankPair_seven_eleven

theorem first_ne_second : first ≠ second := by decide

/-- Two distinct retained spans have the same four endpoint labels. -/
theorem rigidLabelInjectivity_fails :
    ¬AllocatedEndpointTransitionRigidLabelInjective profiles := by
  intro hinjective
  exact first_ne_second
    (hinjective first second fullIdeal first_rigid second_rigid)

/-- Equivalently, the size-two Hall expansion statement fails. -/
theorem pairExpansion_fails :
    ¬AllocatedEndpointTransitionPairExpansion profiles := by
  rw [allocatedEndpointTransitionPairExpansion_iff_rigidLabelInjective]
  exact rigidLabelInjectivity_fails

/-- Hence the full transition-Hall condition fails on the same open node. -/
theorem hall_fails : ¬AllocatedEndpointTransitionHall profiles := by
  intro hhall
  exact pairExpansion_fails
    (allocatedEndpointTransitionHall_implies_pairExpansion hhall)

end StructuralChargingTransitionHallCollision
end ErdosSzekeres

end
