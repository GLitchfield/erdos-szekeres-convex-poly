module

public import ErdosSzekeres.TripleColoringExtension
public import ErdosSzekeres.DecomposableRealization

@[expose] public section

/-!
# Finite realizability of one-change triple colorings

This file separates the geometric necessity of the one-change law from its
finite converse.  The general direction follows from the orientation identity
for a swept configuration.  The first converse is proved completely on four
vertices using all eight allowed sign words and exact rational coordinates.
-/

namespace ErdosSzekeres

noncomputable section

/-- Every sweep-realizable triple coloring satisfies the one-change law on its
complete ordered vertex set. -/
theorem SweptConfiguration.oneChangeOn_univ {n : ℕ}
    (P : SweptConfiguration n) :
    OneChangeOn P.tripleColoring Finset.univ := by
  intro i j k l hij hjk hkl _ _ _ _
  exact P.turnSequenceAllowed i j k l hij hjk hkl

/-- The abstract realizability predicate implies the complete one-change law. -/
theorem IsSweepRealizable.oneChangeOn_univ {n : ℕ} {χ : TripleColoring n}
    (hχ : IsSweepRealizable χ) : OneChangeOn χ Finset.univ := by
  obtain ⟨P, rfl⟩ := hχ
  exact P.oneChangeOn_univ

/-- At size `n`, the one-change law is complete when it characterizes exactly
the triple colorings induced by planar general-position sweep configurations. -/
def OneChangeRealizabilityCompleteAt (n : ℕ) : Prop :=
  ∀ χ : TripleColoring n,
    OneChangeOn χ Finset.univ ↔ IsSweepRealizable χ

def finFourTriple012 : OrderedTriple 4 := ⟨0, 1, 2, by decide, by decide⟩
def finFourTriple013 : OrderedTriple 4 := ⟨0, 1, 3, by decide, by decide⟩
def finFourTriple023 : OrderedTriple 4 := ⟨0, 2, 3, by decide, by decide⟩
def finFourTriple123 : OrderedTriple 4 := ⟨1, 2, 3, by decide, by decide⟩

/-- A coloring on four ordered vertices is determined by its four increasing
triples. -/
theorem TripleColoring.ext_finFour {χ ψ : TripleColoring 4}
    (h012 : χ finFourTriple012 = ψ finFourTriple012)
    (h013 : χ finFourTriple013 = ψ finFourTriple013)
    (h023 : χ finFourTriple023 = ψ finFourTriple023)
    (h123 : χ finFourTriple123 = ψ finFourTriple123) : χ = ψ := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals simp_all [finFourTriple012, finFourTriple013,
    finFourTriple023, finFourTriple123]

/-- Build a four-point sweep configuration from exact ordinates once its four
ordered determinants have been checked. -/
def finFourConfiguration (y : Fin 4 → ℝ)
    (hgp : ∀ i j k : Fin 4, i < j → j < k →
      orientation (ordinatePoint y i) (ordinatePoint y j)
        (ordinatePoint y k) ≠ 0) : SweptConfiguration 4 where
  point := ordinatePoint y
  sweep_strictMono := by
    intro i j hij
    simp only [ordinatePoint_zero]
    exact_mod_cast hij
  generalPosition := generalPosition_of_ordered (ordinatePoint y) hgp

def finFourHeights0 : Fin 4 → ℝ := ![0, 0, -1, -3]
def finFourHeights1 : Fin 4 → ℝ := ![0, 0, 1, -3]
def finFourHeights3 : Fin 4 → ℝ := ![0, -3, -1, -3]
def finFourHeights7 : Fin 4 → ℝ := ![0, -3, -2, -2]
def finFourHeights8 : Fin 4 → ℝ := ![0, 1, -1, -2]
def finFourHeightsC : Fin 4 → ℝ := ![0, 0, -3, -3]
def finFourHeightsE : Fin 4 → ℝ := ![0, -1, -3, -2]
def finFourHeightsF : Fin 4 → ℝ := ![0, -3, -3, -2]

@[simp] theorem finFourHeights0_zero : finFourHeights0 0 = 0 := by rfl
@[simp] theorem finFourHeights0_one : finFourHeights0 1 = 0 := by rfl
@[simp] theorem finFourHeights0_two : finFourHeights0 2 = -1 := by rfl
@[simp] theorem finFourHeights0_three : finFourHeights0 3 = -3 := by rfl

@[simp] theorem finFourHeights1_zero : finFourHeights1 0 = 0 := by rfl
@[simp] theorem finFourHeights1_one : finFourHeights1 1 = 0 := by rfl
@[simp] theorem finFourHeights1_two : finFourHeights1 2 = 1 := by rfl
@[simp] theorem finFourHeights1_three : finFourHeights1 3 = -3 := by rfl

@[simp] theorem finFourHeights3_zero : finFourHeights3 0 = 0 := by rfl
@[simp] theorem finFourHeights3_one : finFourHeights3 1 = -3 := by rfl
@[simp] theorem finFourHeights3_two : finFourHeights3 2 = -1 := by rfl
@[simp] theorem finFourHeights3_three : finFourHeights3 3 = -3 := by rfl

@[simp] theorem finFourHeights7_zero : finFourHeights7 0 = 0 := by rfl
@[simp] theorem finFourHeights7_one : finFourHeights7 1 = -3 := by rfl
@[simp] theorem finFourHeights7_two : finFourHeights7 2 = -2 := by rfl
@[simp] theorem finFourHeights7_three : finFourHeights7 3 = -2 := by rfl

@[simp] theorem finFourHeights8_zero : finFourHeights8 0 = 0 := by rfl
@[simp] theorem finFourHeights8_one : finFourHeights8 1 = 1 := by rfl
@[simp] theorem finFourHeights8_two : finFourHeights8 2 = -1 := by rfl
@[simp] theorem finFourHeights8_three : finFourHeights8 3 = -2 := by rfl

@[simp] theorem finFourHeightsC_zero : finFourHeightsC 0 = 0 := by rfl
@[simp] theorem finFourHeightsC_one : finFourHeightsC 1 = 0 := by rfl
@[simp] theorem finFourHeightsC_two : finFourHeightsC 2 = -3 := by rfl
@[simp] theorem finFourHeightsC_three : finFourHeightsC 3 = -3 := by rfl

@[simp] theorem finFourHeightsE_zero : finFourHeightsE 0 = 0 := by rfl
@[simp] theorem finFourHeightsE_one : finFourHeightsE 1 = -1 := by rfl
@[simp] theorem finFourHeightsE_two : finFourHeightsE 2 = -3 := by rfl
@[simp] theorem finFourHeightsE_three : finFourHeightsE 3 = -2 := by rfl

@[simp] theorem finFourHeightsF_zero : finFourHeightsF 0 = 0 := by rfl
@[simp] theorem finFourHeightsF_one : finFourHeightsF 1 = -3 := by rfl
@[simp] theorem finFourHeightsF_two : finFourHeightsF 2 = -3 := by rfl
@[simp] theorem finFourHeightsF_three : finFourHeightsF 3 = -2 := by rfl

theorem finFourGeneralPosition0 :
    ∀ i j k : Fin 4, i < j → j < k →
      orientation (ordinatePoint finFourHeights0 i)
        (ordinatePoint finFourHeights0 j)
        (ordinatePoint finFourHeights0 k) ≠ 0 := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [finFourHeights0, ordinatePoint, orientation]

theorem finFourGeneralPosition1 :
    ∀ i j k : Fin 4, i < j → j < k →
      orientation (ordinatePoint finFourHeights1 i)
        (ordinatePoint finFourHeights1 j)
        (ordinatePoint finFourHeights1 k) ≠ 0 := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [finFourHeights1, ordinatePoint, orientation]

theorem finFourGeneralPosition3 :
    ∀ i j k : Fin 4, i < j → j < k →
      orientation (ordinatePoint finFourHeights3 i)
        (ordinatePoint finFourHeights3 j)
        (ordinatePoint finFourHeights3 k) ≠ 0 := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [finFourHeights3, ordinatePoint, orientation]

theorem finFourGeneralPosition7 :
    ∀ i j k : Fin 4, i < j → j < k →
      orientation (ordinatePoint finFourHeights7 i)
        (ordinatePoint finFourHeights7 j)
        (ordinatePoint finFourHeights7 k) ≠ 0 := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [finFourHeights7, ordinatePoint, orientation]

theorem finFourGeneralPosition8 :
    ∀ i j k : Fin 4, i < j → j < k →
      orientation (ordinatePoint finFourHeights8 i)
        (ordinatePoint finFourHeights8 j)
        (ordinatePoint finFourHeights8 k) ≠ 0 := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [finFourHeights8, ordinatePoint, orientation]

theorem finFourGeneralPositionC :
    ∀ i j k : Fin 4, i < j → j < k →
      orientation (ordinatePoint finFourHeightsC i)
        (ordinatePoint finFourHeightsC j)
        (ordinatePoint finFourHeightsC k) ≠ 0 := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [finFourHeightsC, ordinatePoint, orientation]

theorem finFourGeneralPositionE :
    ∀ i j k : Fin 4, i < j → j < k →
      orientation (ordinatePoint finFourHeightsE i)
        (ordinatePoint finFourHeightsE j)
        (ordinatePoint finFourHeightsE k) ≠ 0 := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [finFourHeightsE, ordinatePoint, orientation]

theorem finFourGeneralPositionF :
    ∀ i j k : Fin 4, i < j → j < k →
      orientation (ordinatePoint finFourHeightsF i)
        (ordinatePoint finFourHeightsF j)
        (ordinatePoint finFourHeightsF k) ≠ 0 := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [finFourHeightsF, ordinatePoint, orientation]

def finFourConfiguration0 : SweptConfiguration 4 :=
  finFourConfiguration finFourHeights0 finFourGeneralPosition0
def finFourConfiguration1 : SweptConfiguration 4 :=
  finFourConfiguration finFourHeights1 finFourGeneralPosition1
def finFourConfiguration3 : SweptConfiguration 4 :=
  finFourConfiguration finFourHeights3 finFourGeneralPosition3
def finFourConfiguration7 : SweptConfiguration 4 :=
  finFourConfiguration finFourHeights7 finFourGeneralPosition7
def finFourConfiguration8 : SweptConfiguration 4 :=
  finFourConfiguration finFourHeights8 finFourGeneralPosition8
def finFourConfigurationC : SweptConfiguration 4 :=
  finFourConfiguration finFourHeightsC finFourGeneralPositionC
def finFourConfigurationE : SweptConfiguration 4 :=
  finFourConfiguration finFourHeightsE finFourGeneralPositionE
def finFourConfigurationF : SweptConfiguration 4 :=
  finFourConfiguration finFourHeightsF finFourGeneralPositionF

theorem finFourConfiguration0_colors :
    finFourConfiguration0.tripleColoring finFourTriple012 = Turn.right ∧
    finFourConfiguration0.tripleColoring finFourTriple013 = Turn.right ∧
    finFourConfiguration0.tripleColoring finFourTriple023 = Turn.right ∧
    finFourConfiguration0.tripleColoring finFourTriple123 = Turn.right := by
  norm_num [finFourConfiguration0, finFourConfiguration,
    finFourTriple012, finFourTriple013, finFourTriple023, finFourTriple123,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    ordinatePoint, orientation]

theorem finFourConfiguration1_colors :
    finFourConfiguration1.tripleColoring finFourTriple012 = Turn.left ∧
    finFourConfiguration1.tripleColoring finFourTriple013 = Turn.right ∧
    finFourConfiguration1.tripleColoring finFourTriple023 = Turn.right ∧
    finFourConfiguration1.tripleColoring finFourTriple123 = Turn.right := by
  norm_num [finFourConfiguration1, finFourConfiguration,
    finFourTriple012, finFourTriple013, finFourTriple023, finFourTriple123,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    ordinatePoint, orientation]

theorem finFourConfiguration3_colors :
    finFourConfiguration3.tripleColoring finFourTriple012 = Turn.left ∧
    finFourConfiguration3.tripleColoring finFourTriple013 = Turn.left ∧
    finFourConfiguration3.tripleColoring finFourTriple023 = Turn.right ∧
    finFourConfiguration3.tripleColoring finFourTriple123 = Turn.right := by
  norm_num [finFourConfiguration3, finFourConfiguration,
    finFourTriple012, finFourTriple013, finFourTriple023, finFourTriple123,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    ordinatePoint, orientation]

theorem finFourConfiguration7_colors :
    finFourConfiguration7.tripleColoring finFourTriple012 = Turn.left ∧
    finFourConfiguration7.tripleColoring finFourTriple013 = Turn.left ∧
    finFourConfiguration7.tripleColoring finFourTriple023 = Turn.left ∧
    finFourConfiguration7.tripleColoring finFourTriple123 = Turn.right := by
  norm_num [finFourConfiguration7, finFourConfiguration,
    finFourTriple012, finFourTriple013, finFourTriple023, finFourTriple123,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    ordinatePoint, orientation]

theorem finFourConfiguration8_colors :
    finFourConfiguration8.tripleColoring finFourTriple012 = Turn.right ∧
    finFourConfiguration8.tripleColoring finFourTriple013 = Turn.right ∧
    finFourConfiguration8.tripleColoring finFourTriple023 = Turn.right ∧
    finFourConfiguration8.tripleColoring finFourTriple123 = Turn.left := by
  norm_num [finFourConfiguration8, finFourConfiguration,
    finFourTriple012, finFourTriple013, finFourTriple023, finFourTriple123,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    ordinatePoint, orientation]

theorem finFourConfigurationC_colors :
    finFourConfigurationC.tripleColoring finFourTriple012 = Turn.right ∧
    finFourConfigurationC.tripleColoring finFourTriple013 = Turn.right ∧
    finFourConfigurationC.tripleColoring finFourTriple023 = Turn.left ∧
    finFourConfigurationC.tripleColoring finFourTriple123 = Turn.left := by
  norm_num [finFourConfigurationC, finFourConfiguration,
    finFourTriple012, finFourTriple013, finFourTriple023, finFourTriple123,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    ordinatePoint, orientation]

theorem finFourConfigurationE_colors :
    finFourConfigurationE.tripleColoring finFourTriple012 = Turn.right ∧
    finFourConfigurationE.tripleColoring finFourTriple013 = Turn.left ∧
    finFourConfigurationE.tripleColoring finFourTriple023 = Turn.left ∧
    finFourConfigurationE.tripleColoring finFourTriple123 = Turn.left := by
  norm_num [finFourConfigurationE, finFourConfiguration,
    finFourTriple012, finFourTriple013, finFourTriple023, finFourTriple123,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    ordinatePoint, orientation]

theorem finFourConfigurationF_colors :
    finFourConfigurationF.tripleColoring finFourTriple012 = Turn.left ∧
    finFourConfigurationF.tripleColoring finFourTriple013 = Turn.left ∧
    finFourConfigurationF.tripleColoring finFourTriple023 = Turn.left ∧
    finFourConfigurationF.tripleColoring finFourTriple123 = Turn.left := by
  norm_num [finFourConfigurationF, finFourConfiguration,
    finFourTriple012, finFourTriple013, finFourTriple023, finFourTriple123,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    ordinatePoint, orientation]

/-- Every allowed four-point sign word has one of the eight explicit rational
sweep realizations above. -/
theorem isSweepRealizable_finFour_of_turnSequenceAllowed
    (χ : TripleColoring 4)
    (h : TurnSequenceAllowed
      (χ finFourTriple012) (χ finFourTriple013)
      (χ finFourTriple023) (χ finFourTriple123)) :
    IsSweepRealizable χ := by
  rcases h with hF | h7 | h3 | h1 | h0 | h8 | hC | hE
  · refine ⟨finFourConfigurationF, ?_⟩
    apply TripleColoring.ext_finFour
    all_goals simp_all [finFourConfigurationF_colors]
  · refine ⟨finFourConfiguration7, ?_⟩
    apply TripleColoring.ext_finFour
    all_goals simp_all [finFourConfiguration7_colors]
  · refine ⟨finFourConfiguration3, ?_⟩
    apply TripleColoring.ext_finFour
    all_goals simp_all [finFourConfiguration3_colors]
  · refine ⟨finFourConfiguration1, ?_⟩
    apply TripleColoring.ext_finFour
    all_goals simp_all [finFourConfiguration1_colors]
  · refine ⟨finFourConfiguration0, ?_⟩
    apply TripleColoring.ext_finFour
    all_goals simp_all [finFourConfiguration0_colors]
  · refine ⟨finFourConfiguration8, ?_⟩
    apply TripleColoring.ext_finFour
    all_goals simp_all [finFourConfiguration8_colors]
  · refine ⟨finFourConfigurationC, ?_⟩
    apply TripleColoring.ext_finFour
    all_goals simp_all [finFourConfigurationC_colors]
  · refine ⟨finFourConfigurationE, ?_⟩
    apply TripleColoring.ext_finFour
    all_goals simp_all [finFourConfigurationE_colors]

/-- On four vertices, the complete rank-three one-change law is equivalent to
straight-line sweep realizability. -/
theorem oneChangeRealizabilityCompleteAt_four :
    OneChangeRealizabilityCompleteAt 4 := by
  intro χ
  constructor
  · intro hχ
    apply isSweepRealizable_finFour_of_turnSequenceAllowed χ
    exact hχ (i := 0) (j := 1) (k := 2) (l := 3)
      (by decide) (by decide) (by decide)
      (by simp) (by simp) (by simp) (by simp)
  · exact IsSweepRealizable.oneChangeOn_univ

end

end ErdosSzekeres

end
