module

public import ErdosSzekeres.RankProfileAmbientEndpoint
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# A realizable counterexample to the single ambient-downset producer

The exact rational nine-point configuration in this file is strong-six-free,
but none of its sixteen clipped ambient pair-rank cells, nor any complement,
is both half-sized and strong-five-free.  The finite checks below use the
transparent pair-rank recurrence and are connected explicitly to
`RankProfile.InVertexDownset`.
-/

namespace ErdosSzekeres
namespace RankProfileAmbientEndpointCounterexample

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- Twice the vertical coordinates of the frozen rational configuration. -/
def heightTwice : Fin 9 → ℤ := ![0, 0, -4, -4, -1, 1, 1, 4, 4]

/-- Twice the signed area after clearing the common denominator in the
vertical coordinates. -/
def orientationTwice (i j k : Fin 9) : ℤ :=
  ((j.val : ℤ) - (i.val : ℤ)) * (heightTwice k - heightTwice i) -
    (heightTwice j - heightTwice i) * ((k.val : ℤ) - (i.val : ℤ))

/-- The executable coloring of the frozen rational configuration. -/
def color : TripleColoring 9 := fun t ↦
  if 0 < orientationTwice t.i t.j t.k then Turn.left else Turn.right

noncomputable section

/-- The exact nine rational points from the independently checked certificate. -/
def points : Fin 9 → Point 2 := ![
  ![0, 0], ![1, 0], ![2, -2], ![3, -2], ![4, -(1 : ℝ) / 2],
  ![5, (1 : ℝ) / 2], ![6, (1 : ℝ) / 2], ![7, 2], ![8, 2]]

/-- The frozen points, with strict sweep order and general position proved
directly over the rational coordinates. -/
noncomputable def configuration : SweptConfiguration 9 where
  point := points
  sweep_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num [points]
  generalPosition := generalPosition_of_ordered points (by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals norm_num at hij
    all_goals norm_num at hjk
    all_goals norm_num [points, orientation])

/-- The geometric coloring agrees with the executable integer-area coloring. -/
theorem configuration_coloring : configuration.tripleColoring = color := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [configuration, points, color, orientationTwice, heightTwice,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn, orientation]

theorem color_sweepRealizable : IsSweepRealizable color :=
  ⟨configuration, configuration_coloring⟩

/-- An executable version of the exact ambient vertex-downset predicate. -/
def inVertexDownsetBool {n : ℕ} (chi : TripleColoring n)
    (s : Finset (Fin n)) (clip : ℕ) (v : Fin n) (cap cup : ℕ) : Bool :=
  decide (1 ≤ cap ∧ cap ≤ clip ∧ 1 ≤ cup ∧ cup ≤ clip) &&
    (List.finRange n).any fun u ↦
      RankProfile.finitePairRankAboveBool chi Turn.right s u v (cap - 1) &&
        RankProfile.finitePairRankAboveBool chi Turn.left s u v (cup - 1)

/-- The finite recurrence computes the unchanged ambient-downset definition. -/
theorem inVertexDownsetBool_eq_true_iff {n : ℕ} (chi : TripleColoring n)
    (s : Finset (Fin n)) (clip : ℕ) (v : Fin n) (cap cup : ℕ) :
    inVertexDownsetBool chi s clip v cap cup = true ↔
      RankProfile.InVertexDownset
        (RankProfile.turnOfColoring chi) s clip v cap cup := by
  constructor
  · intro h
    rw [inVertexDownsetBool, Bool.and_eq_true] at h
    rcases h with ⟨hbounds, hwitness⟩
    have hbounds' : 1 ≤ cap ∧ cap ≤ clip ∧ 1 ≤ cup ∧ cup ≤ clip :=
      of_decide_eq_true hbounds
    rcases hbounds' with ⟨hcapOne, hcapClip, hcupOne, hcupClip⟩
    rw [List.any_eq_true] at hwitness
    obtain ⟨u, _huRange, hranks⟩ := hwitness
    rw [Bool.and_eq_true] at hranks
    rcases hranks with ⟨hright, hleft⟩
    have hcapRank :=
      (RankProfile.hasFinitePairRankAbove_iff_hasPairRankAtLeast
        chi Turn.right s u v (cap - 1)).mp hright
    have hcupRank :=
      (RankProfile.hasFinitePairRankAbove_iff_hasPairRankAtLeast
        chi Turn.left s u v (cup - 1)).mp hleft
    rw [Nat.sub_add_cancel hcapOne] at hcapRank
    rw [Nat.sub_add_cancel hcupOne] at hcupRank
    have hu : u ∈ s := by
      obtain ⟨pre, _hchain, hin, _hlength⟩ := hcapRank
      exact hin u (by simp)
    have huv : u < v := by
      obtain ⟨pre, hchain, _hin, _hlength⟩ := hcapRank
      have hsuffix := hchain.1.right_of_append (l₁ := pre) (l₂ := [u, v])
      simpa using hsuffix
    exact ⟨hcapOne, hcupOne, u, hu, huv,
      ⟨hcapClip, hcapRank⟩, ⟨hcupClip, hcupRank⟩⟩
  · rintro ⟨hcapOne, hcupOne, u, _hu, _huv,
      ⟨hcapClip, hcapRank⟩, ⟨hcupClip, hcupRank⟩⟩
    rw [inVertexDownsetBool, Bool.and_eq_true]
    constructor
    · exact decide_eq_true ⟨hcapOne, hcapClip, hcupOne, hcupClip⟩
    · rw [List.any_eq_true]
      refine ⟨u, List.mem_finRange u, ?_⟩
      rw [Bool.and_eq_true]
      constructor
      · apply (RankProfile.hasFinitePairRankAbove_iff_hasPairRankAtLeast
          chi Turn.right s u v (cap - 1)).mpr
        rwa [Nat.sub_add_cancel hcapOne]
      · apply (RankProfile.hasFinitePairRankAbove_iff_hasPairRankAtLeast
          chi Turn.left s u v (cup - 1)).mpr
        rwa [Nat.sub_add_cancel hcupOne]

/-- A clipped full-ambient threshold cell, computed through the transparent
finite pair-rank recurrence. -/
def thresholdCell {n : ℕ} (chi : TripleColoring n) (clip cap cup : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun v ↦
    inVertexDownsetBool chi Finset.univ clip v cap cup = true

@[simp] theorem mem_thresholdCell_iff {n : ℕ} (chi : TripleColoring n)
    (clip cap cup : ℕ) (v : Fin n) :
    v ∈ thresholdCell chi clip cap cup ↔
      RankProfile.InVertexDownset
        (RankProfile.turnOfColoring chi) Finset.univ clip v cap cup := by
  simp only [thresholdCell, Finset.mem_filter, Finset.mem_univ, true_and]
  exact inVertexDownsetBool_eq_true_iff chi Finset.univ clip v cap cup

/-- The exact complement alternative allowed by the producer. -/
def thresholdCellComplement {n : ℕ} (chi : TripleColoring n)
    (clip cap cup : ℕ) : Finset (Fin n) :=
  Finset.univ \ thresholdCell chi clip cap cup

@[simp] theorem mem_thresholdCellComplement_iff {n : ℕ}
    (chi : TripleColoring n) (clip cap cup : ℕ) (v : Fin n) :
    v ∈ thresholdCellComplement chi clip cap cup ↔
      ¬RankProfile.InVertexDownset
        (RankProfile.turnOfColoring chi) Finset.univ clip v cap cup := by
  simp [thresholdCellComplement]

theorem color_noStrongSetBool_six :
    ∀ s : Finset (Fin 9), s.card = 6 →
      RankProfileCollision.strongPolygonSetBool color s = false := by
  decide

theorem color_noStrongSix :
    ¬ContainsStrongPolygonSet color Finset.univ 6 := by
  rintro ⟨polygon, _hsub, hcard, hstrong⟩
  have htrue :=
    (RankProfileCollision.strongPolygonSetBool_eq_true_iff color polygon).2
      hstrong
  rw [color_noStrongSetBool_six polygon hcard] at htrue
  contradiction

/-- The strong-five witness used by each half-sized downset cell.  Its value on
the twelve smaller cells is irrelevant. -/
def downsetStrongFiveWitness (cap cup : Fin 4) : Finset (Fin 9) :=
  if cap = 0 ∧ cup = 0 then {1, 2, 3, 5, 6}
  else if cap = 0 ∧ cup = 1 then {3, 4, 5, 6, 7}
  else if cap = 0 ∧ cup = 2 then {4, 5, 6, 7, 8}
  else if cap = 1 ∧ cup = 0 then {2, 3, 5, 6, 7}
  else {0, 1, 2, 3, 4}

/-- A common strong-five witness for every half-sized complement cell. -/
def complementStrongFiveWitness : Finset (Fin 9) := {0, 1, 2, 3, 4}

/-- Exhaustive certificate for the sixteen downset cells. -/
theorem thresholdCell_failure_certificate :
    ∀ cap cup : Fin 4,
      2 * (thresholdCell color 4 (cap.val + 1) (cup.val + 1)).card < 9 ∨
        downsetStrongFiveWitness cap cup ⊆
            thresholdCell color 4 (cap.val + 1) (cup.val + 1) ∧
          (downsetStrongFiveWitness cap cup).card = 5 ∧
          RankProfileCollision.strongPolygonSetBool color
            (downsetStrongFiveWitness cap cup) = true := by
  decide

/-- Exhaustive certificate for the sixteen exact complements. -/
theorem thresholdCellComplement_failure_certificate :
    ∀ cap cup : Fin 4,
      2 * (thresholdCellComplement color 4
          (cap.val + 1) (cup.val + 1)).card < 9 ∨
        complementStrongFiveWitness ⊆
            thresholdCellComplement color 4 (cap.val + 1) (cup.val + 1) ∧
          complementStrongFiveWitness.card = 5 ∧
          RankProfileCollision.strongPolygonSetBool color
            complementStrongFiveWitness = true := by
  decide

end
end RankProfileAmbientEndpointCounterexample

/-- The frozen rational Fin9 configuration refutes the unchanged single-cell
full-ambient threshold producer. -/
theorem not_ambientDownsetThresholdHalfSupportAtSix :
    ¬AmbientDownsetThresholdHalfSupportAtSix := by
  intro hthreshold
  obtain ⟨cap, cup, support, hcapOne, hcapFour, hcupOne, hcupFour,
      hsupport, hfree, hhalf⟩ :=
    hthreshold
      RankProfileAmbientEndpointCounterexample.color_sweepRealizable
      RankProfileAmbientEndpointCounterexample.color_noStrongSix
  let capIndex : Fin 4 := ⟨cap - 1, by omega⟩
  let cupIndex : Fin 4 := ⟨cup - 1, by omega⟩
  have hcapIndex : capIndex.val + 1 = cap := by
    simp [capIndex]
    omega
  have hcupIndex : cupIndex.val + 1 = cup := by
    simp [cupIndex]
    omega
  rcases hsupport with hdownset | hcomplement
  · have hsupportEq : support =
        RankProfileAmbientEndpointCounterexample.thresholdCell
          RankProfileAmbientEndpointCounterexample.color 4 cap cup := by
      ext v
      rw [RankProfileAmbientEndpointCounterexample.mem_thresholdCell_iff]
      exact hdownset v
    rw [hsupportEq] at hfree hhalf
    have hfailure :=
      RankProfileAmbientEndpointCounterexample.thresholdCell_failure_certificate
        capIndex cupIndex
    rw [hcapIndex, hcupIndex] at hfailure
    rcases hfailure with hsmall | ⟨hsub, hcard, hstrong⟩
    · omega
    · apply hfree
      exact ⟨_, hsub, hcard,
        (RankProfileCollision.strongPolygonSetBool_eq_true_iff _ _).1 hstrong⟩
  · have hsupportEq : support =
        RankProfileAmbientEndpointCounterexample.thresholdCellComplement
          RankProfileAmbientEndpointCounterexample.color 4 cap cup := by
      ext v
      rw [RankProfileAmbientEndpointCounterexample.mem_thresholdCellComplement_iff]
      exact hcomplement v
    rw [hsupportEq] at hfree hhalf
    have hfailure :=
      RankProfileAmbientEndpointCounterexample.thresholdCellComplement_failure_certificate
        capIndex cupIndex
    rw [hcapIndex, hcupIndex] at hfailure
    rcases hfailure with hsmall | ⟨hsub, hcard, hstrong⟩
    · omega
    · apply hfree
      exact ⟨_, hsub, hcard,
        (RankProfileCollision.strongPolygonSetBool_eq_true_iff _ _).1 hstrong⟩

end ErdosSzekeres

end
