module

public import ErdosSzekeres.StructuralChargingMiddleSplitBridges

@[expose] public section

/-!
# A realizable middle-split bridge countermodel

The rational coordinates below realize the independently checked twelve-point
`no-extreme` SAT coloring from experiment 0022.  This file first establishes
the exact bridge from that finite coloring to a genuine swept planar
configuration.  Further finite properties should be promoted separately so
that realizability is not conflated with the SAT replay.
-/

namespace ErdosSzekeres

noncomputable section

def middleSplitRealizationLeftCodes : List ℕ := [
  14, 15, 18, 19, 20, 27, 30, 31, 32, 42, 43, 44, 53, 54, 55, 56, 66, 67,
  68, 171, 174, 175, 176, 186, 187, 188, 197, 198, 199, 200, 210, 211, 212,
  262, 263, 275, 330, 331, 341, 342, 343, 344, 347, 354, 355, 356, 406, 407,
  419, 485, 486, 487, 488, 489, 490, 491, 498, 499, 500, 550, 551, 563, 642,
  643, 694, 695, 707, 838, 839, 851, 957, 958, 959, 969, 970, 971, 982, 983,
  995, 1113, 1114, 1115, 1126, 1127, 1139, 1270, 1271, 1283, 1427]

def middleSplitRealizationColor : TripleColoring 12 := fun t =>
  if 144 * t.i.val + 12 * t.j.val + t.k.val ∈
      middleSplitRealizationLeftCodes then Turn.left else Turn.right

noncomputable def middleSplitRealizationPoints : Fin 12 → Point 2 := ![
  ![0, 0],
  ![884, (709 : ℝ) / 1250000],
  ![1607, (636673 : ℝ) / 500000000],
  ![2528, (2651561 : ℝ) / 1000000000],
  ![3422, (414487 : ℝ) / 500000000],
  ![3704, (341 : ℝ) / 160000],
  ![4512, (14418149 : ℝ) / 1000000000],
  ![4792, (875299 : ℝ) / 100000000],
  ![4928, (1475013 : ℝ) / 250000000],
  ![5371, (22909 : ℝ) / 200000000],
  ![6285, (38437 : ℝ) / 1000000000],
  ![7139, 0]]

set_option maxHeartbeats 4000000 in
noncomputable def middleSplitRealizationConfiguration : SweptConfiguration 12 where
  point := middleSplitRealizationPoints
  sweep_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num [middleSplitRealizationPoints]
  generalPosition := generalPosition_of_ordered middleSplitRealizationPoints (by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals norm_num at hij
    all_goals norm_num at hjk
    all_goals norm_num [middleSplitRealizationPoints, orientation])

set_option maxHeartbeats 4000000 in
theorem middleSplitRealizationConfiguration_coloring :
    middleSplitRealizationConfiguration.tripleColoring =
      middleSplitRealizationColor := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [middleSplitRealizationConfiguration,
    middleSplitRealizationPoints, SweptConfiguration.tripleColoring,
    SweptConfiguration.turn, middleSplitRealizationColor,
    middleSplitRealizationLeftCodes, orientation]

/-- The exact twelve-point `no-extreme` coloring is realized by rational
straight-line coordinates in general position and in the prescribed sweep
order. -/
theorem middleSplitRealizationColor_isSweepRealizable :
    IsSweepRealizable middleSplitRealizationColor :=
  ⟨middleSplitRealizationConfiguration,
    middleSplitRealizationConfiguration_coloring⟩

end
end ErdosSzekeres

end
