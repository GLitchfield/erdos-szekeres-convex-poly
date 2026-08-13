module

public import ErdosSzekeres.RankProfile
public import ErdosSzekeres.StrongPredecessorBicoloring

@[expose] public section

/-!
# Full-ambient endpoint extension for pair-rank downsets

The local theorem in this file retains the ambient coloring and the two incoming
endpoints.  It deliberately does not factor through a clipped child rank state.
The final definition records the stronger threshold producer that would turn
this local infrastructure into the existing predecessor-half-subset contract.
-/

namespace ErdosSzekeres
namespace RankProfile

variable {α : Type*} [LinearOrder α]

/-- Extending an ordered pair by one same-turn vertex raises its consecutive
pair-rank threshold by one. -/
theorem HasPairRankAtLeast.extend_right
    {κ : α → α → α → Turn} {c : Turn} {s : Finset α}
    {u x y : α} {r : ℕ} (hrank : HasPairRankAtLeast κ c s u x r)
    (hy : y ∈ s) (hxy : x < y) (hturn : κ u x y = c) :
    HasPairRankAtLeast κ c s x y (r + 1) := by
  obtain ⟨pre, hchain, hin, hlength⟩ := hrank
  refine ⟨pre ++ [u], ?_, ?_, ?_⟩
  · rw [List.append_assoc]
    simpa using (CupCap.isTurnChain_append_cons3.mpr
      ⟨hchain, hturn, CupCap.isTurnChain_pair.mpr hxy⟩)
  · intro z hz
    simp at hz
    rcases hz with hz | hzu | hzx | hzy
    · exact hin z (by simp [hz])
    · simpa [hzu] using hin u (by simp)
    · simpa [hzx] using hin x (by simp)
    · simpa [hzy] using hy
  · simp at hlength ⊢
    omega

/-- The clipped form of `HasPairRankAtLeast.extend_right`.  Nonsaturation is
the exact condition needed to retain the successor threshold inside the clip. -/
theorem HasClippedPairRankAtLeast.extend_right
    {κ : α → α → α → Turn} {c : Turn} {s : Finset α}
    {clip : ℕ} {u x y : α} {r : ℕ}
    (hrank : HasClippedPairRankAtLeast κ c s clip u x r)
    (hnonsat : r < clip) (hy : y ∈ s) (hxy : x < y)
    (hturn : κ u x y = c) :
    HasClippedPairRankAtLeast κ c s clip x y (r + 1) := by
  exact ⟨by omega, hrank.2.extend_right hy hxy hturn⟩

/-- Nonsaturated coordinate-maximal incoming ranks either create a strict
full-ambient downset difference at the next endpoint, or their two selected
incoming endpoints cross. -/
theorem ambientEndpoint_separated_or_crossed
    (κ : α → α → α → Turn) (s : Finset α) (clip : ℕ)
    {uCap uCup x y : α} {cap cup : ℕ}
    (huCap : uCap ∈ s) (huCup : uCup ∈ s) (hx : x ∈ s) (hy : y ∈ s)
    (huCapX : uCap < x) (huCupX : uCup < x) (hxy : x < y)
    (hcapOne : 1 ≤ cap) (hcupOne : 1 ≤ cup)
    (hcapNonsat : cap < clip) (hcupNonsat : cup < clip)
    (hcapRank : HasClippedPairRankAtLeast κ Turn.right s clip uCap x cap)
    (hcupRank : HasClippedPairRankAtLeast κ Turn.left s clip uCup x cup)
    (hcapMax : ¬InVertexDownset κ s clip x (cap + 1) 1)
    (hcupMax : ¬InVertexDownset κ s clip x 1 (cup + 1)) :
    (∃ a b, InVertexDownset κ s clip y a b ∧
      ¬InVertexDownset κ s clip x a b) ∨
    (κ uCap x y = Turn.left ∧ κ uCup x y = Turn.right) := by
  by_cases hcapTurn : κ uCap x y = Turn.right
  · left
    refine ⟨cap + 1, 1, ?_, hcapMax⟩
    refine ⟨by omega, by omega, x, hx, hxy, ?_, ?_⟩
    · exact hcapRank.extend_right hcapNonsat hy hxy hcapTurn
    · exact ⟨by omega, hasPairRankAtLeast_one κ Turn.left hx hy hxy⟩
  · have hcapCross : κ uCap x y = Turn.left := by
      simpa only [Turn.ne_right_iff_eq_left] using hcapTurn
    by_cases hcupTurn : κ uCup x y = Turn.left
    · left
      refine ⟨1, cup + 1, ?_, hcupMax⟩
      refine ⟨by omega, by omega, x, hx, hxy, ?_, ?_⟩
      · exact ⟨by omega, hasPairRankAtLeast_one κ Turn.right hx hy hxy⟩
      · exact hcupRank.extend_right hcupNonsat hy hxy hcupTurn
    · right
      have hcupCross : κ uCup x y = Turn.right := by
        cases hturn : κ uCup x y with
        | left => exact (hcupTurn hturn).elim
        | right => rfl
      exact ⟨hcapCross, hcupCross⟩

end RankProfile

/-- At `k = 6`, one threshold cell (or its complement) is a predecessor-free
half-support.  This is the exact producer still needed beyond the local
endpoint dichotomy; it contains no same-`k` upper-bound premise. -/
def AmbientDownsetThresholdHalfSupportAtSix : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ 6 →
    ∃ cap cup : ℕ, ∃ support : Finset (Fin n),
      1 ≤ cap ∧ cap ≤ 4 ∧ 1 ≤ cup ∧ cup ≤ 4 ∧
      ((∀ v, v ∈ support ↔ RankProfile.InVertexDownset
          (RankProfile.turnOfColoring χ) Finset.univ 4 v cap cup) ∨
        (∀ v, v ∈ support ↔ ¬RankProfile.InVertexDownset
          (RankProfile.turnOfColoring χ) Finset.univ 4 v cap cup)) ∧
      ¬ContainsStrongPolygonSet χ support 5 ∧
      n ≤ 2 * support.card

/-- The full-ambient threshold producer feeds the existing exact recurrence
interface without using `SweepExactUpperAt 6` or assuming the conclusion. -/
theorem predecessorHalfSubsetAt_six_of_ambientDownsetThresholdHalfSupport
    (hthreshold : AmbientDownsetThresholdHalfSupportAtSix) :
    PredecessorHalfSubsetAt 6 := by
  intro n χ hreal hfree
  obtain ⟨_cap, _cup, support, _, _, _, _, _, hsupportFree, hhalf⟩ :=
    hthreshold hreal hfree
  exact ⟨support, by simpa using hsupportFree, hhalf⟩

end ErdosSzekeres

end
