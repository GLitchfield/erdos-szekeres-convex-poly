module

public import ErdosSzekeres.RootedChainFootprint

@[expose] public section

/-!
# Dominance pruning for rooted chain spans

The raw rooted-chain footprint records a rank at every exact endpoint pair.
For a singleton extension, many of those records are redundant.  At a fixed
far endpoint, a chain of at least as large a rank whose near endpoint is
farther toward the singleton enables every extension enabled by the weaker
chain.

This file isolates that sound pruning rule.  It is the first formal component
of the proposed dominance quotient; it does not assert that the remaining
frontier has size bounded only by the target polygon size.
-/

namespace ErdosSzekeres

noncomputable section

/-- A left-extension state dominates another when its left endpoint lies no
farther left and its certified rank is no smaller. -/
def LeftExtensionDominates {n : ℕ}
    (dominantLeft : Fin n) (dominantRank : ℕ)
    (dominatedLeft : Fin n) (dominatedRank : ℕ) : Prop :=
  dominatedLeft ≤ dominantLeft ∧ dominatedRank ≤ dominantRank

/-- A right-extension state dominates another when its right endpoint lies no
farther right and its certified rank is no smaller. -/
def RightExtensionDominates {n : ℕ}
    (dominantRight : Fin n) (dominantRank : ℕ)
    (dominatedRight : Fin n) (dominatedRank : ℕ) : Prop :=
  dominantRight ≤ dominatedRight ∧ dominatedRank ≤ dominantRank

/-- A crossing port dominates another on both extension sides when its left
endpoint is nearer from the left, its right endpoint is nearer from the right,
and its certified rank is no smaller. -/
def TwoSidedExtensionDominates {leftSize rightSize : ℕ}
    (dominantLeft : Fin leftSize) (dominantRight : Fin rightSize) (dominantRank : ℕ)
    (dominatedLeft : Fin leftSize) (dominatedRight : Fin rightSize) (dominatedRank : ℕ) :
    Prop :=
  dominatedLeft ≤ dominantLeft ∧ dominantRight ≤ dominatedRight ∧
    dominatedRank ≤ dominantRank

/-- Equal-rank diagonal crossing ports dominate one another only when they are
the same port. Since `m` is arbitrary, two-sided dominance alone admits
arbitrarily large antichains and cannot give an ambient-independent frontier
bound. -/
theorem twoSidedExtensionDominates_diagonal_iff {m : ℕ} (i j : Fin m) (rank : ℕ) :
    TwoSidedExtensionDominates i i rank j j rank ↔ i = j := by
  grind [TwoSidedExtensionDominates]

/-- Lowering a requested cup-rank threshold preserves a span witness. -/
theorem HasCupSpanRankAtLeast.anti_rank {n : ℕ} {chi : TripleColoring n}
    {s : Finset (Fin n)} {a b : Fin n} {dominantRank dominatedRank : ℕ}
    (h : HasCupSpanRankAtLeast chi s a b dominantRank)
    (hrank : dominatedRank ≤ dominantRank) :
    HasCupSpanRankAtLeast chi s a b dominatedRank := by
  obtain ⟨cup, hcupSub, hcard, hcup, hspan⟩ := h
  exact ⟨cup, hcupSub, hrank.trans hcard, hcup, hspan⟩

/-- Lowering a requested cap-rank threshold preserves a span witness. -/
theorem HasCapSpanRankAtLeast.anti_rank {n : ℕ} {chi : TripleColoring n}
    {s : Finset (Fin n)} {a b : Fin n} {dominantRank dominatedRank : ℕ}
    (h : HasCapSpanRankAtLeast chi s a b dominantRank)
    (hrank : dominatedRank ≤ dominantRank) :
    HasCapSpanRankAtLeast chi s a b dominatedRank := by
  obtain ⟨cap, hcapSub, hcard, hcap, hspan⟩ := h
  exact ⟨cap, hcapSub, hrank.trans hcard, hcap, hspan⟩

/-- A dominant lower cup span supplies every upper-singleton left extension
supplied by the dominated endpoint/rank pair. -/
theorem HasCupSpanRankAtLeast.insert_upper_left_of_dominates {n : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {dominantLeft dominatedLeft b q : Fin n}
    {dominantRank dominatedRank : ℕ}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hspan : HasCupSpanRankAtLeast chi lower dominantLeft b dominantRank)
    (hdom : LeftExtensionDominates dominantLeft dominantRank
      dominatedLeft dominatedRank)
    (hqUpper : q ∈ upper) (hq : q < dominatedLeft) :
    HasCupSpanRankAtLeast chi (lower ∪ upper) q b (dominatedRank + 1) := by
  rcases hdom with ⟨hleft, hrank⟩
  refine (hspan.insert_upper_left hdeep hqUpper (hq.trans_le hleft)).anti_rank ?_
  omega

/-- A dominant lower cup span supplies every upper-singleton right extension
supplied by the dominated endpoint/rank pair. -/
theorem HasCupSpanRankAtLeast.insert_upper_right_of_dominates {n : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {a dominantRight dominatedRight q : Fin n}
    {dominantRank dominatedRank : ℕ}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hspan : HasCupSpanRankAtLeast chi lower a dominantRight dominantRank)
    (hdom : RightExtensionDominates dominantRight dominantRank
      dominatedRight dominatedRank)
    (hqUpper : q ∈ upper) (hq : dominatedRight < q) :
    HasCupSpanRankAtLeast chi (lower ∪ upper) a q (dominatedRank + 1) := by
  rcases hdom with ⟨hright, hrank⟩
  refine (hspan.insert_upper_right hdeep hqUpper (hright.trans_lt hq)).anti_rank ?_
  omega

/-- A dominant upper cap span supplies every lower-singleton left extension
supplied by the dominated endpoint/rank pair. -/
theorem HasCapSpanRankAtLeast.insert_lower_left_of_dominates {n : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {dominantLeft dominatedLeft b q : Fin n}
    {dominantRank dominatedRank : ℕ}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hspan : HasCapSpanRankAtLeast chi upper dominantLeft b dominantRank)
    (hdom : LeftExtensionDominates dominantLeft dominantRank
      dominatedLeft dominatedRank)
    (hqLower : q ∈ lower) (hq : q < dominatedLeft) :
    HasCapSpanRankAtLeast chi (lower ∪ upper) q b (dominatedRank + 1) := by
  rcases hdom with ⟨hleft, hrank⟩
  refine (hspan.insert_lower_left hdeep hqLower (hq.trans_le hleft)).anti_rank ?_
  omega

/-- A dominant upper cap span supplies every lower-singleton right extension
supplied by the dominated endpoint/rank pair. -/
theorem HasCapSpanRankAtLeast.insert_lower_right_of_dominates {n : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {a dominantRight dominatedRight q : Fin n}
    {dominantRank dominatedRank : ℕ}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hspan : HasCapSpanRankAtLeast chi upper a dominantRight dominantRank)
    (hdom : RightExtensionDominates dominantRight dominantRank
      dominatedRight dominatedRank)
    (hqLower : q ∈ lower) (hq : dominatedRight < q) :
    HasCapSpanRankAtLeast chi (lower ∪ upper) a q (dominatedRank + 1) := by
  rcases hdom with ⟨hright, hrank⟩
  refine (hspan.insert_lower_right hdeep hqLower (hright.trans_lt hq)).anti_rank ?_
  omega

end

end ErdosSzekeres
