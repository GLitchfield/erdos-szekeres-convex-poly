module

public import ErdosSzekeres.StructuralChargingRankTwoGenealogy
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# A ten-point counterexample to the adjusted promotion capacity

The first hidden-gap promotion census stopped at eight vertices.  This file
kernel-checks the first obstruction beyond that range.  An open decomposable
ten-point root has seven minimal crossing cap spans and four promoted hidden
lower gaps, all of exact ambient rank three.  Thus the adjusted demand has at
least eleven members, while the proposed `k = 7`, rank-three Pascal layer has
only ten slots.
-/

namespace ErdosSzekeres
namespace StructuralChargingAdjustedCounterexample

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def lowerTree : RankProfileCollision.DecompositionTree 10 :=
  .node
    (.node
      (.node
        (.node (.leaf 8) (.leaf 4))
        (.leaf 6))
      (.leaf 2))
    (.leaf 0)

def upperTree : RankProfileCollision.DecompositionTree 10 :=
  .node
    (.node
      (.node
        (.node (.leaf 9) (.leaf 7))
        (.leaf 5))
      (.leaf 3))
    (.leaf 1)

def tree : RankProfileCollision.DecompositionTree 10 := .node lowerTree upperTree

def color : TripleColoring 10 := tree.coloring

def lower : Finset (Fin 10) := lowerTree.vertices

def upper : Finset (Fin 10) := upperTree.vertices

def support : Finset (Fin 10) := lower ∪ upper

theorem root_deep : HasDeepBelowSplit color lower upper := by
  exact RankProfileCollision.DecompositionTree.node_split lowerTree upperTree (by decide)

theorem support_eq_univ : support = Finset.univ := by decide

theorem tree_wellFormed : RankProfileCollision.DecompositionTree.WellFormed tree := by
  simp [tree, lowerTree, upperTree, RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem decomposable_support : IsDecomposableOn color support := by
  have h := RankProfileCollision.DecompositionTree.decomposableOn tree tree_wellFormed
  simpa [color, support, lower, upper, tree,
    RankProfileCollision.DecompositionTree.vertices] using h

theorem no_strong_seven_bool :
    ∀ polygon : Finset (Fin 10), polygon.card = 7 →
      RankProfileCollision.strongPolygonSetBool color polygon = false := by
  decide

theorem no_strong_seven : ¬ContainsStrongPolygonSet color support 7 := by
  rintro ⟨polygon, _, hcard, hstrong⟩
  have hfalse := no_strong_seven_bool polygon hcard
  have htrue :=
    (RankProfileCollision.strongPolygonSetBool_eq_true_iff color polygon).2 hstrong
  rw [hfalse] at htrue
  contradiction

/-- Executable monochromaticity check for the concrete ten-point coloring. -/
def turnSetBool (s : Finset (Fin 10)) (turn : Turn) : Bool :=
  (List.finRange 10).all fun i ↦
    (List.finRange 10).all fun j ↦
      (List.finRange 10).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              decide (color ⟨i, j, k, hij, hjk⟩ = turn)
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 10)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 10, t.i ∈ s → t.j ∈ s → t.k ∈ s → color t = turn := by
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

theorem isCapSet_of_turnSetBool {s : Finset (Fin 10)}
    (h : turnSetBool s .right = true) : IsCapSet color s := by
  simpa [IsCapSet] using (turnSetBool_eq_true_iff s .right).mp h

theorem not_isCapSet_of_turnSetBool_false {s : Finset (Fin 10)}
    (h : turnSetBool s .right = false) : ¬IsCapSet color s := by
  intro hcap
  have htrue : turnSetBool s .right = true :=
    (turnSetBool_eq_true_iff s .right).mpr (by simpa [IsCapSet] using hcap)
  rw [h] at htrue
  contradiction

theorem sweepSpan_card_le_interval {chain : Finset (Fin 10)} {a b : Fin 10}
    (hspan : HasSweepSpan chain a b) : chain.card ≤ b.val + 1 - a.val := by
  calc
    chain.card ≤ (Finset.Icc a b).card := by
      apply Finset.card_le_card
      intro x hx
      exact Finset.mem_Icc.mpr
        ⟨hspan.left_endpoint x hx, hspan.right_endpoint x hx⟩
    _ = b.val + 1 - a.val := Fin.card_Icc a b

theorem hasSweepSpan_of_subset_Icc {chain : Finset (Fin 10)} {a b : Fin 10}
    (hlt : a < b) (ha : a ∈ chain) (hb : b ∈ chain)
    (hsub : chain ⊆ Finset.Icc a b) : HasSweepSpan chain a b := by
  exact ⟨hlt, ha, hb,
    fun x hx ↦ (Finset.mem_Icc.mp (hsub hx)).1,
    fun x hx ↦ (Finset.mem_Icc.mp (hsub hx)).2⟩

theorem capSpanRankThree_of_triple (a q b : Fin 10)
    (haq : a < q) (hqb : q < b)
    (hcap : turnSetBool {a, q, b} .right = true) :
    HasSpanRankAtLeast .right color support ⟨a, b⟩ 3 := by
  refine ⟨{a, q, b}, ?_, ?_, isCapSet_of_turnSetBool hcap, ?_⟩
  · simp [support_eq_univ]
  · simp [haq.ne, hqb.ne, (haq.trans hqb).ne]
  · exact hasSweepSpan_of_subset_Icc (haq.trans hqb) (by simp) (by simp) (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_Icc.mpr ⟨le_rfl, (haq.trans hqb).le⟩
      · exact Finset.mem_Icc.mpr ⟨haq.le, hqb.le⟩
      · exact Finset.mem_Icc.mpr ⟨(haq.trans hqb).le, le_rfl⟩)

theorem capSpan_exactRankThree_of_width_two (a q b : Fin 10)
    (haq : a < q) (hqb : q < b) (hwidth : b.val = a.val + 2)
    (hcap : turnSetBool {a, q, b} .right = true) :
    HasExactSpanRank .right color support ⟨a, b⟩ 3 := by
  constructor
  · exact capSpanRankThree_of_triple a q b haq hqb hcap
  · rintro ⟨chain, _, hcard, _, hspan⟩
    have hbound := sweepSpan_card_le_interval hspan
    change chain.card ≤ b.val + 1 - a.val at hbound
    omega

theorem capSpan_exactRankThree_of_width_three (a q b : Fin 10)
    (haq : a < q) (hqb : q < b) (hwidth : b.val = a.val + 3)
    (hcap : turnSetBool {a, q, b} .right = true)
    (hnotCap : ¬IsCapSet color (Finset.Icc a b)) :
    HasExactSpanRank .right color support ⟨a, b⟩ 3 := by
  constructor
  · exact capSpanRankThree_of_triple a q b haq hqb hcap
  · rintro ⟨chain, _, hcard, hchainCap, hspan⟩
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
    apply hnotCap
    simpa [← heq] using hchainCap

theorem mem_lower_iff_even (x : Fin 10) : x ∈ lower ↔ x.val % 2 = 0 := by
  fin_cases x <;> decide

theorem mem_upper_iff_odd (x : Fin 10) : x ∈ upper ↔ x.val % 2 = 1 := by
  fin_cases x <;> decide

theorem crossing_not_width_two {span : SweepSpanEndpoints 10}
    (hcross : span.CrossesSplit lower upper) :
    span.right.val ≠ span.left.val + 2 := by
  intro hwidth
  rcases hcross.2 with hsides | hsides
  · rw [mem_lower_iff_even] at hsides
    rw [mem_upper_iff_odd] at hsides
    omega
  · rw [mem_upper_iff_odd] at hsides
    rw [mem_lower_iff_even] at hsides
    omega

theorem widthThree_exactRankThree_mem_frontier (span : SweepSpanEndpoints 10)
    (hcross : span.CrossesSplit lower upper)
    (hexact : HasExactSpanRank .right color support span 3)
    (hwidth : span.right.val = span.left.val + 3) :
    span ∈ allocatedExactRankFrontier color lower upper .right 3 := by
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
    have hleft := hcontains.1
    have hright := hcontains.2
    have hleftVal : span.left.val ≤ other.left.val := hleft
    have hrightVal : other.right.val ≤ span.right.val := hright
    have hotherWidth : other.right.val = other.left.val + 3 := by omega
    have hleftEq : other.left.val = span.left.val := by omega
    have hrightEq : other.right.val = span.right.val := by omega
    cases span
    cases other
    simp only at hleftEq hrightEq ⊢
    congr
    · exact Fin.ext hleftEq
    · exact Fin.ext hrightEq

def crossingSpans : Finset (SweepSpanEndpoints 10) :=
  {⟨0, 3⟩, ⟨1, 4⟩, ⟨2, 5⟩, ⟨3, 6⟩, ⟨4, 7⟩, ⟨5, 8⟩, ⟨6, 9⟩}

def promotedSpans : Finset (SweepSpanEndpoints 10) :=
  {⟨0, 2⟩, ⟨2, 4⟩, ⟨4, 6⟩, ⟨6, 8⟩}

theorem exact_zero_three :
    HasExactSpanRank .right color support ⟨0, 3⟩ 3 := by
  apply capSpan_exactRankThree_of_width_three 0 1 3 <;> try decide
  exact not_isCapSet_of_turnSetBool_false (by decide)

theorem exact_one_four :
    HasExactSpanRank .right color support ⟨1, 4⟩ 3 := by
  apply capSpan_exactRankThree_of_width_three 1 3 4 <;> try decide
  exact not_isCapSet_of_turnSetBool_false (by decide)

theorem exact_two_five :
    HasExactSpanRank .right color support ⟨2, 5⟩ 3 := by
  apply capSpan_exactRankThree_of_width_three 2 3 5 <;> try decide
  exact not_isCapSet_of_turnSetBool_false (by decide)

theorem exact_three_six :
    HasExactSpanRank .right color support ⟨3, 6⟩ 3 := by
  apply capSpan_exactRankThree_of_width_three 3 5 6 <;> try decide
  exact not_isCapSet_of_turnSetBool_false (by decide)

theorem exact_four_seven :
    HasExactSpanRank .right color support ⟨4, 7⟩ 3 := by
  apply capSpan_exactRankThree_of_width_three 4 5 7 <;> try decide
  exact not_isCapSet_of_turnSetBool_false (by decide)

theorem exact_five_eight :
    HasExactSpanRank .right color support ⟨5, 8⟩ 3 := by
  apply capSpan_exactRankThree_of_width_three 5 7 8 <;> try decide
  exact not_isCapSet_of_turnSetBool_false (by decide)

theorem exact_six_nine :
    HasExactSpanRank .right color support ⟨6, 9⟩ 3 := by
  apply capSpan_exactRankThree_of_width_three 6 7 9 <;> try decide
  exact not_isCapSet_of_turnSetBool_false (by decide)

theorem exact_zero_two :
    HasExactSpanRank .right color support ⟨0, 2⟩ 3 := by
  exact capSpan_exactRankThree_of_width_two 0 1 2 (by decide) (by decide)
    (by decide) (by decide)

theorem exact_two_four :
    HasExactSpanRank .right color support ⟨2, 4⟩ 3 := by
  exact capSpan_exactRankThree_of_width_two 2 3 4 (by decide) (by decide)
    (by decide) (by decide)

theorem exact_four_six :
    HasExactSpanRank .right color support ⟨4, 6⟩ 3 := by
  exact capSpan_exactRankThree_of_width_two 4 5 6 (by decide) (by decide)
    (by decide) (by decide)

theorem exact_six_eight :
    HasExactSpanRank .right color support ⟨6, 8⟩ 3 := by
  exact capSpan_exactRankThree_of_width_two 6 7 8 (by decide) (by decide)
    (by decide) (by decide)

theorem crossingSpans_subset_frontier :
    crossingSpans ⊆ allocatedExactRankFrontier color lower upper .right 3 := by
  intro span hspan
  simp only [crossingSpans, Finset.mem_insert, Finset.mem_singleton] at hspan
  rcases hspan with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact widthThree_exactRankThree_mem_frontier _
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ exact_zero_three (by decide)
  · exact widthThree_exactRankThree_mem_frontier _
      ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩ exact_one_four (by decide)
  · exact widthThree_exactRankThree_mem_frontier _
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ exact_two_five (by decide)
  · exact widthThree_exactRankThree_mem_frontier _
      ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩ exact_three_six (by decide)
  · exact widthThree_exactRankThree_mem_frontier _
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ exact_four_seven (by decide)
  · exact widthThree_exactRankThree_mem_frontier _
      ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩ exact_five_eight (by decide)
  · exact widthThree_exactRankThree_mem_frontier _
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ exact_six_nine (by decide)

theorem hidden_zero_two :
    IsHiddenLowerGap lower upper (⟨0, 2⟩ : SweepSpanEndpoints 10) := by
  refine ⟨⟨by decide, by decide, by decide, ?_⟩, 1, by decide, by decide, by decide⟩
  intro q hq
  fin_cases q <;>
    norm_num [lower, lowerTree, RankProfileCollision.DecompositionTree.vertices] at hq ⊢ <;>
    omega

theorem hidden_two_four :
    IsHiddenLowerGap lower upper (⟨2, 4⟩ : SweepSpanEndpoints 10) := by
  refine ⟨⟨by decide, by decide, by decide, ?_⟩, 3, by decide, by decide, by decide⟩
  intro q hq
  fin_cases q <;>
    norm_num [lower, lowerTree, RankProfileCollision.DecompositionTree.vertices] at hq ⊢ <;>
    omega

theorem hidden_four_six :
    IsHiddenLowerGap lower upper (⟨4, 6⟩ : SweepSpanEndpoints 10) := by
  refine ⟨⟨by decide, by decide, by decide, ?_⟩, 5, by decide, by decide, by decide⟩
  intro q hq
  fin_cases q <;>
    norm_num [lower, lowerTree, RankProfileCollision.DecompositionTree.vertices] at hq ⊢ <;>
    omega

theorem hidden_six_eight :
    IsHiddenLowerGap lower upper (⟨6, 8⟩ : SweepSpanEndpoints 10) := by
  refine ⟨⟨by decide, by decide, by decide, ?_⟩, 7, by decide, by decide, by decide⟩
  intro q hq
  fin_cases q <;>
    norm_num [lower, lowerTree, RankProfileCollision.DecompositionTree.vertices] at hq ⊢ <;>
    omega

theorem promoted_zero_two_mem :
    (⟨0, 2⟩ : SweepSpanEndpoints 10) ∈
      promotedExactRankSources .right color lower upper 3 := by
  rw [mem_promotedExactRankSources]
  exact ⟨mem_hiddenGapSources_iff.mpr hidden_zero_two, exact_zero_two⟩

theorem promoted_two_four_mem :
    (⟨2, 4⟩ : SweepSpanEndpoints 10) ∈
      promotedExactRankSources .right color lower upper 3 := by
  rw [mem_promotedExactRankSources]
  exact ⟨mem_hiddenGapSources_iff.mpr hidden_two_four, exact_two_four⟩

theorem promoted_four_six_mem :
    (⟨4, 6⟩ : SweepSpanEndpoints 10) ∈
      promotedExactRankSources .right color lower upper 3 := by
  rw [mem_promotedExactRankSources]
  exact ⟨mem_hiddenGapSources_iff.mpr hidden_four_six, exact_four_six⟩

theorem promoted_six_eight_mem :
    (⟨6, 8⟩ : SweepSpanEndpoints 10) ∈
      promotedExactRankSources .right color lower upper 3 := by
  rw [mem_promotedExactRankSources]
  exact ⟨mem_hiddenGapSources_iff.mpr hidden_six_eight, exact_six_eight⟩

theorem promotedSpans_subset_sources :
    promotedSpans ⊆ promotedExactRankSources .right color lower upper 3 := by
  intro span hspan
  simp only [promotedSpans, Finset.mem_insert, Finset.mem_singleton] at hspan
  rcases hspan with rfl | rfl | rfl | rfl
  · exact promoted_zero_two_mem
  · exact promoted_two_four_mem
  · exact promoted_four_six_mem
  · exact promoted_six_eight_mem

/-- The adjusted rank-three carrier already exceeds its Pascal layer in an
open decomposable `k = 7` context. -/
theorem adjusted_rank_three_demand_exceeds_pascal :
    publishedSpanPascalDemand 7 3 <
      Fintype.card (AdjustedHigherRankDemand (rank := 3) .right color lower upper) := by
  rw [adjustedHigherRankDemand_card]
  have hcross := Finset.card_le_card crossingSpans_subset_frontier
  have hpromoted := Finset.card_le_card promotedSpans_subset_sources
  have hcrossCard : crossingSpans.card = 7 := by decide
  have hpromotedCard : promotedSpans.card = 4 := by decide
  rw [hcrossCard] at hcross
  rw [hpromotedCard] at hpromoted
  norm_num [publishedSpanPascalDemand, Nat.choose]
  omega

/-- The exact adjusted Hall contract selected after the eight-vertex gate is
false in the concrete ten-point context. -/
theorem not_adjusted_rank_three_endpointRankTransitionHall :
    ¬AdjustedHigherRankDemand.EndpointRankTransitionHall
      (chi := color) (lower := lower) (upper := upper) (color := .right)
      (rank := 3) (k := 7) (by norm_num) (by norm_num) := by
  intro hhall
  have hcapacity :=
    AdjustedHigherRankDemand.card_le_publishedSpanPascalDemand_of_endpointRankTransitionHall
      (chi := color) (lower := lower) (upper := upper) (color := .right)
      (rank := 3) (k := 7) (by norm_num) (by norm_num) hhall
  rw [← adjustedHigherRankDemand_card] at hcapacity
  exact (Nat.not_lt_of_ge hcapacity) adjusted_rank_three_demand_exceeds_pascal

/-- No alternative matching argument can inject this additive demand into the
unchanged rank-three Pascal layer. -/
theorem no_adjusted_rank_three_slotting :
    IsEmpty (AdjustedHigherRankDemand.Slotting
      (chi := color) (lower := lower) (upper := upper) (color := .right) 3 7) := by
  constructor
  intro slotting
  have hcard := Fintype.card_le_of_injective slotting.slot slotting.injective
  have hslots : Fintype.card (AllocatedPascalSlot 3 7) =
      publishedSpanPascalDemand 7 3 := by
    simp [publishedSpanPascalDemand]
  rw [hslots] at hcard
  exact (Nat.not_lt_of_ge hcard) adjusted_rank_three_demand_exceeds_pascal

end StructuralChargingAdjustedCounterexample
end ErdosSzekeres

end
