module

public import ErdosSzekeres.StructuralChargingAdjustedCounterexample
public import ErdosSzekeres.StructuralChargingTransitionHallRayBridge

@[expose] public section

/-!
# Counterexample to single-coefficient cross-color reuse

The ten-point adjusted-promotion obstruction has seven crossing spans of exact
rank three in both colors.  Identifying the cap and cup requests at each common
endpoint pair repairs the finite candidate graph, but it does not repair the
published induction:

* the active cup ray lies in the lower child while the active cap ray lies in
  the disjoint upper child, so no nonempty retained subset belongs to both
  published child cores; and
* at `k = 7`, rank three, the two threshold increments cost two copies of the
  ten-element Pascal coefficient.  Replacing them by one copy gives the false
  inequality `32 <= 22`.

Thus common endpoints alone do not justify the proposed cross-color quotient.
This file does not rule out a stronger joint geometric invariant whose payoff
is not the sum of the two published child increments.
-/

namespace ErdosSzekeres
namespace StructuralChargingCrossColorReuseCounterexample

open StructuralChargingAdjustedCounterexample

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Executable cup monochromaticity for the concrete ten-point coloring. -/
theorem isCupSet_of_turnSetBool {s : Finset (Fin 10)}
    (h : turnSetBool s .left = true) : IsCupSet color s := by
  simpa [IsCupSet] using (turnSetBool_eq_true_iff s .left).mp h

/-- A false executable cup test refutes cup monochromaticity. -/
theorem not_isCupSet_of_turnSetBool_false {s : Finset (Fin 10)}
    (h : turnSetBool s .left = false) : ¬IsCupSet color s := by
  intro hcup
  have htrue : turnSetBool s .left = true :=
    (turnSetBool_eq_true_iff s .left).mpr (by simpa [IsCupSet] using hcup)
  rw [h] at htrue
  contradiction

/-- A concrete cup triple supplies a rank-three span witness. -/
theorem cupSpanRankThree_of_triple (a q b : Fin 10)
    (haq : a < q) (hqb : q < b)
    (hcup : turnSetBool {a, q, b} .left = true) :
    HasSpanRankAtLeast .left color support ⟨a, b⟩ 3 := by
  refine ⟨{a, q, b}, ?_, ?_, isCupSet_of_turnSetBool hcup, ?_⟩
  · simp [support_eq_univ]
  · simp [haq.ne, hqb.ne, (haq.trans hqb).ne]
  · exact hasSweepSpan_of_subset_Icc (haq.trans hqb) (by simp) (by simp) (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_Icc.mpr ⟨le_rfl, (haq.trans hqb).le⟩
      · exact Finset.mem_Icc.mpr ⟨haq.le, hqb.le⟩
      · exact Finset.mem_Icc.mpr ⟨(haq.trans hqb).le, le_rfl⟩)

/-- On an interval of four sweep positions, a cup triple and failure of the
whole interval to be a cup give exact cup rank three. -/
theorem cupSpan_exactRankThree_of_width_three (a q b : Fin 10)
    (haq : a < q) (hqb : q < b) (hwidth : b.val = a.val + 3)
    (hcup : turnSetBool {a, q, b} .left = true)
    (hnotCup : ¬IsCupSet color (Finset.Icc a b)) :
    HasExactSpanRank .left color support ⟨a, b⟩ 3 := by
  constructor
  · exact cupSpanRankThree_of_triple a q b haq hqb hcup
  · rintro ⟨chain, _, hcard, hchainCup, hspan⟩
    have hsub : chain ⊆ Finset.Icc a b := by
      intro x hx
      exact Finset.mem_Icc.mpr
        ⟨hspan.left_endpoint x hx, hspan.right_endpoint x hx⟩
    have hbound := sweepSpan_card_le_interval hspan
    change chain.card ≤ b.val + 1 - a.val at hbound
    have hchainCard : chain.card = 4 := by omega
    have hintervalCard : (Finset.Icc a b).card = 4 := by
      rw [Fin.card_Icc]
      omega
    have heq : chain = Finset.Icc a b :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    apply hnotCup
    simpa [← heq] using hchainCup

/-- A width-three crossing span of exact cup rank three is inclusion-minimal
among exact-rank crossing cup spans. -/
theorem widthThree_exactCupRankThree_mem_frontier
    (span : SweepSpanEndpoints 10)
    (hcross : span.CrossesSplit lower upper)
    (hexact : HasExactSpanRank .left color support span 3)
    (hwidth : span.right.val = span.left.val + 3) :
    span ∈ allocatedExactRankFrontier color lower upper .left 3 := by
  rw [mem_allocatedExactRankFrontier]
  constructor
  · rw [mem_allocatedExactRankSpans]
    simpa [support] using And.intro hcross hexact
  · intro other hother hcontains
    have hotherData := mem_allocatedExactRankSpans.mp hother
    obtain ⟨chain, _, hcard, _, hchainSpan⟩ := hotherData.2.1
    have hbound := sweepSpan_card_le_interval hchainSpan
    change chain.card ≤ other.right.val + 1 - other.left.val at hbound
    have hotherNotTwo := crossing_not_width_two hotherData.1
    have hleftVal : span.left.val ≤ other.left.val := hcontains.1
    have hrightVal : other.right.val ≤ span.right.val := hcontains.2
    have hotherWidth : other.right.val = other.left.val + 3 := by omega
    have hleftEq : other.left.val = span.left.val := by omega
    have hrightEq : other.right.val = span.right.val := by omega
    cases span
    cases other
    simp only at hleftEq hrightEq ⊢
    congr
    · exact Fin.ext hleftEq
    · exact Fin.ext hrightEq

theorem cup_exact_zero_three :
    HasExactSpanRank .left color support ⟨0, 3⟩ 3 := by
  apply cupSpan_exactRankThree_of_width_three 0 2 3 <;> try decide
  exact not_isCupSet_of_turnSetBool_false (by decide)

theorem cup_exact_one_four :
    HasExactSpanRank .left color support ⟨1, 4⟩ 3 := by
  apply cupSpan_exactRankThree_of_width_three 1 2 4 <;> try decide
  exact not_isCupSet_of_turnSetBool_false (by decide)

theorem cup_exact_two_five :
    HasExactSpanRank .left color support ⟨2, 5⟩ 3 := by
  apply cupSpan_exactRankThree_of_width_three 2 4 5 <;> try decide
  exact not_isCupSet_of_turnSetBool_false (by decide)

theorem cup_exact_three_six :
    HasExactSpanRank .left color support ⟨3, 6⟩ 3 := by
  apply cupSpan_exactRankThree_of_width_three 3 4 6 <;> try decide
  exact not_isCupSet_of_turnSetBool_false (by decide)

theorem cup_exact_four_seven :
    HasExactSpanRank .left color support ⟨4, 7⟩ 3 := by
  apply cupSpan_exactRankThree_of_width_three 4 6 7 <;> try decide
  exact not_isCupSet_of_turnSetBool_false (by decide)

theorem cup_exact_five_eight :
    HasExactSpanRank .left color support ⟨5, 8⟩ 3 := by
  apply cupSpan_exactRankThree_of_width_three 5 6 8 <;> try decide
  exact not_isCupSet_of_turnSetBool_false (by decide)

theorem cup_exact_six_nine :
    HasExactSpanRank .left color support ⟨6, 9⟩ 3 := by
  apply cupSpan_exactRankThree_of_width_three 6 8 9 <;> try decide
  exact not_isCupSet_of_turnSetBool_false (by decide)

/-- The seven cap/rank-three crossing spans in the ten-point obstruction are
also cup/rank-three frontier spans. -/
theorem crossingSpans_subset_cup_frontier :
    crossingSpans ⊆ allocatedExactRankFrontier color lower upper .left 3 := by
  intro span hspan
  simp only [crossingSpans, Finset.mem_insert, Finset.mem_singleton] at hspan
  rcases hspan with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact widthThree_exactCupRankThree_mem_frontier _
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ cup_exact_zero_three (by decide)
  · exact widthThree_exactCupRankThree_mem_frontier _
      ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩ cup_exact_one_four (by decide)
  · exact widthThree_exactCupRankThree_mem_frontier _
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ cup_exact_two_five (by decide)
  · exact widthThree_exactCupRankThree_mem_frontier _
      ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩ cup_exact_three_six (by decide)
  · exact widthThree_exactCupRankThree_mem_frontier _
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ cup_exact_four_seven (by decide)
  · exact widthThree_exactCupRankThree_mem_frontier _
      ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩ cup_exact_five_eight (by decide)
  · exact widthThree_exactCupRankThree_mem_frontier _
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ cup_exact_six_nine (by decide)

/-- There are at least seven genuine common cap/cup rank-three frontier
obligations in the ten-point obstruction. -/
theorem seven_le_common_rank_three_frontier :
    7 ≤ (allocatedExactRankFrontier color lower upper .right 3 ∩
      allocatedExactRankFrontier color lower upper .left 3).card := by
  have hsubset : crossingSpans ⊆
      allocatedExactRankFrontier color lower upper .right 3 ∩
        allocatedExactRankFrontier color lower upper .left 3 := by
    intro span hspan
    exact Finset.mem_inter.mpr
      ⟨crossingSpans_subset_frontier hspan,
        crossingSpans_subset_cup_frontier hspan⟩
  have hcard := Finset.card_le_card hsubset
  have hcrossingCard : crossingSpans.card = 7 := by decide
  omega

/-- Every recorded common frontier span exposes both exact active rays: its
cup ray is supported in the lower child and its cap ray in the upper child, as
made explicit by `AllocatedExactRankActiveRay`. -/
theorem crossingSpan_has_both_activeRays {span : SweepSpanEndpoints 10}
    (hspan : span ∈ crossingSpans) :
    AllocatedExactRankActiveRay (rank := 3) color lower upper .left span ∧
      AllocatedExactRankActiveRay (rank := 3) color lower upper .right span := by
  constructor
  · exact allocatedExactRankSpan_has_activeRay root_deep (by omega)
      ((mem_allocatedExactRankFrontier.mp
        (crossingSpans_subset_cup_frontier hspan)).1)
  · exact allocatedExactRankSpan_has_activeRay root_deep (by omega)
      ((mem_allocatedExactRankFrontier.mp
        (crossingSpans_subset_frontier hspan)).1)

/-- A proposed semantic implementation of cross-color reuse by one nonempty
retained subset contained in both published child cores. -/
structure PublishedCrossColorSharedSeed {alpha : Type*} {a u k : Nat}
    {lowerChild upperChild : Finset alpha}
    (cupSlice : PublishedChildSlice a u k lowerChild)
    (capSlice : PublishedCapChildSlice a u k upperChild) where
  seed : Finset alpha
  seed_nonempty : seed.Nonempty
  seed_subset_cup_core : seed ⊆ cupSlice.core
  seed_subset_cap_core : seed ⊆ capSlice.core

/-- Published cores retained from disjoint children are themselves disjoint. -/
theorem published_child_slice_cores_disjoint
    {alpha : Type*} [DecidableEq alpha] {a u k : Nat}
    {lowerChild upperChild : Finset alpha}
    (hdisjoint : Disjoint lowerChild upperChild)
    (cupSlice : PublishedChildSlice a u k lowerChild)
    (capSlice : PublishedCapChildSlice a u k upperChild) :
    Disjoint cupSlice.core capSlice.core :=
  hdisjoint.mono cupSlice.core_subset capSlice.core_subset

/-- Consequently no nonempty retained subset can literally pay both the cup
and cap child requests at one common endpoint span. -/
theorem no_publishedCrossColorSharedSeed_of_disjoint
    {alpha : Type*} [DecidableEq alpha] {a u k : Nat}
    {lowerChild upperChild : Finset alpha}
    (hdisjoint : Disjoint lowerChild upperChild)
    (cupSlice : PublishedChildSlice a u k lowerChild)
    (capSlice : PublishedCapChildSlice a u k upperChild) :
    IsEmpty (PublishedCrossColorSharedSeed cupSlice capSlice) := by
  constructor
  intro resource
  obtain ⟨x, hx⟩ := resource.seed_nonempty
  exact (Finset.disjoint_left.mp
      (published_child_slice_cores_disjoint hdisjoint cupSlice capSlice))
    (resource.seed_subset_cup_core hx)
    (resource.seed_subset_cap_core hx)

/-- At the bounded `k = 7`, rank-three gate, the two actual successor
thresholds total 32, whereas the two base thresholds plus only one copy of the
rank-three Pascal demand total 22. -/
theorem crossColor_single_rank_three_demand_arithmetic_k7 :
    decomposableThreshold 7 4 7 + decomposableThreshold 4 7 7 = 32 ∧
      decomposableThreshold 7 3 7 + decomposableThreshold 3 7 7 +
        publishedSpanPascalDemand 7 3 = 22 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow,
    publishedSpanPascalDemand, Nat.choose, Finset.sum_Icc_succ_top]

/-- Therefore one shared coefficient cannot pay the two published child
increments, even when a cap and cup obligation have identical endpoints. -/
theorem crossColor_single_rank_three_demand_insufficient_k7 :
    ¬(decomposableThreshold 7 4 7 + decomposableThreshold 4 7 7 ≤
      decomposableThreshold 7 3 7 + decomposableThreshold 3 7 7 +
        publishedSpanPascalDemand 7 3) := by
  have h := crossColor_single_rank_three_demand_arithmetic_k7
  omega

end StructuralChargingCrossColorReuseCounterexample
end ErdosSzekeres

end
