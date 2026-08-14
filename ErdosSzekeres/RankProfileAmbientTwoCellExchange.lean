module

public import ErdosSzekeres.RankProfileAmbientEndpoint

@[expose] public section

/-!
# Local defect descent for two ambient rank cells

This file formalizes the proof-independent consumer for the adaptive two-cell
support card.  A classifier consists of two ordered clip-four down-set cells
and a Boolean function of their two membership bits.  The frozen producer says
that every half-sized classifier containing a strong five has a nearby
half-sized classifier with strictly fewer strong five-subsets.

The consumer starts at the constant-true classifier and descends in the
natural-valued defect.  It therefore does not select a successful classifier
by inspecting all classifiers, and it uses no same-`k` upper bound.
-/

namespace ErdosSzekeres

/-- Two ordered clip-four ambient cells together with a Boolean truth table.
There are `4^4 * 2^4 = 4096` values of this type. -/
structure AmbientTwoCellClassifier where
  firstCap : Fin 4
  firstCup : Fin 4
  secondCap : Fin 4
  secondCup : Fin 4
  truth00 : Bool
  truth01 : Bool
  truth10 : Bool
  truth11 : Bool
deriving DecidableEq

namespace AmbientTwoCellClassifier

/-- Evaluate the four-entry truth table in `00, 01, 10, 11` order. -/
def truth (classifier : AmbientTwoCellClassifier) : Bool × Bool → Bool
  | (false, false) => classifier.truth00
  | (false, true) => classifier.truth01
  | (true, false) => classifier.truth10
  | (true, true) => classifier.truth11

/-- The Boolean combination of the classifier's two full-ambient down-set
cells.  Threshold indices are shifted from `Fin 4` to the range `1..4`. -/
noncomputable def support {n : ℕ} (classifier : AmbientTwoCellClassifier)
    (χ : TripleColoring n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun vertex ↦
    classifier.truth
      (decide (RankProfile.InVertexDownset
        (RankProfile.turnOfColoring χ) Finset.univ 4 vertex
          (classifier.firstCap.val + 1) (classifier.firstCup.val + 1)),
       decide (RankProfile.InVertexDownset
        (RankProfile.turnOfColoring χ) Finset.univ 4 vertex
          (classifier.secondCap.val + 1) (classifier.secondCup.val + 1))) = true

/-- The exact number of strong five-subsets in a classifier's support. -/
noncomputable def strongFiveDefect {n : ℕ}
    (classifier : AmbientTwoCellClassifier) (χ : TripleColoring n) : ℕ := by
  classical
  exact ((Finset.univ.powersetCard 5).filter fun polygon ↦
    polygon ⊆ classifier.support χ ∧ IsStrongPolygonSet χ polygon).card

/-- Hamming distance between the two four-entry truth tables. -/
def truthDistance (first second : AmbientTwoCellClassifier) : ℕ :=
  (if first.truth00 = second.truth00 then 0 else 1) +
    (if first.truth01 = second.truth01 then 0 else 1) +
    (if first.truth10 = second.truth10 then 0 else 1) +
    (if first.truth11 = second.truth11 then 0 else 1)

/-- Natural absolute difference, used on threshold indices. -/
def coordinateDistance (first second : Fin 4) : ℕ :=
  first.val - second.val + (second.val - first.val)

/-- The path metric whose distance-one steps change one cell coordinate by one
or flip one truth-table entry. -/
def distance (first second : AmbientTwoCellClassifier) : ℕ :=
  coordinateDistance first.firstCap second.firstCap +
    coordinateDistance first.firstCup second.firstCup +
    coordinateDistance first.secondCap second.secondCap +
    coordinateDistance first.secondCup second.secondCup +
    truthDistance first second

/-- A classifier selecting the entire vertex set. -/
def allSupport : AmbientTwoCellClassifier where
  firstCap := 0
  firstCup := 0
  secondCap := 0
  secondCup := 0
  truth00 := true
  truth01 := true
  truth10 := true
  truth11 := true

@[simp] theorem support_allSupport {n : ℕ} (χ : TripleColoring n) :
    allSupport.support χ = Finset.univ := by
  classical
  ext vertex
  simp [support, allSupport, truth]
  generalize decide (RankProfile.InVertexDownset
    (RankProfile.turnOfColoring χ) Finset.univ 4 vertex 1 1) = value
  cases value <;> rfl

/-- Defect zero is exactly the absence of a strong five in the support. -/
theorem strongFiveDefect_eq_zero_iff {n : ℕ} (χ : TripleColoring n)
    (classifier : AmbientTwoCellClassifier) :
    classifier.strongFiveDefect χ = 0 ↔
      ¬ContainsStrongPolygonSet χ (classifier.support χ) 5 := by
  classical
  constructor
  · intro hzero hcontains
    rcases hcontains with ⟨polygon, hsubset, hcard, hstrong⟩
    have hmem : polygon ∈ (Finset.univ.powersetCard 5).filter (fun candidate ↦
        candidate ⊆ classifier.support χ ∧ IsStrongPolygonSet χ candidate) := by
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ polygon, hcard⟩, hsubset, hstrong⟩
    exact (Finset.card_ne_zero.mpr ⟨polygon, hmem⟩) hzero
  · intro hfree
    rw [strongFiveDefect, Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨polygon, hmem⟩
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hmem
    exact hfree ⟨polygon, hmem.2.1, hmem.1.2, hmem.2.2⟩

end AmbientTwoCellClassifier

/-- The adaptive two-cell support card, separated from any proposed way to
produce the classifier. -/
def AmbientDownsetTwoCellBooleanHalfSupportAtSix : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ 6 →
    ∃ classifier : AmbientTwoCellClassifier,
      ¬ContainsStrongPolygonSet χ (classifier.support χ) 5 ∧
      n ≤ 2 * (classifier.support χ).card

/-- Frozen local-descent producer.  Radius one is primary in computation and
radius two is its sole predeclared fallback. -/
def AmbientTwoCellDefectDescentAtSix (radius : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ 6 →
    ∀ classifier : AmbientTwoCellClassifier,
      n ≤ 2 * (classifier.support χ).card →
      0 < classifier.strongFiveDefect χ →
      ∃ improved : AmbientTwoCellClassifier,
        AmbientTwoCellClassifier.distance classifier improved ≤ radius ∧
        n ≤ 2 * (improved.support χ).card ∧
        improved.strongFiveDefect χ < classifier.strongFiveDefect χ

/-- A natural-valued strict descent from one admissible starting point reaches
an admissible point of value zero. -/
theorem exists_zero_of_strict_descent {index : Type*} (value : index → ℕ)
    (admissible : index → Prop) (initial : index) (hinitial : admissible initial)
    (hdescent : ∀ current, admissible current → 0 < value current →
      ∃ improved, admissible improved ∧ value improved < value current) :
    ∃ result, admissible result ∧ value result = 0 := by
  have findZero : ∀ bound current, value current = bound → admissible current →
      ∃ result, admissible result ∧ value result = 0 := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current hvalue hcurrent
      by_cases hzero : value current = 0
      · exact ⟨current, hcurrent, hzero⟩
      · obtain ⟨improved, himproved, hlower⟩ :=
          hdescent current hcurrent (Nat.pos_of_ne_zero hzero)
        have himprovedBound : value improved < bound := by
          simpa [hvalue] using hlower
        exact ih (value improved) himprovedBound improved rfl himproved
  exact findZero (value initial) initial rfl hinitial

/-- Local defect descent supplies the adaptive two-cell support card. -/
theorem ambientDownsetTwoCellBooleanHalfSupportAtSix_of_defectDescent
    {radius : ℕ} (hdescent : AmbientTwoCellDefectDescentAtSix radius) :
    AmbientDownsetTwoCellBooleanHalfSupportAtSix := by
  intro n χ hreal hfree
  let initial := AmbientTwoCellClassifier.allSupport
  have hinitial : n ≤ 2 * (initial.support χ).card := by
    simp [initial]
    omega
  obtain ⟨classifier, hhalf, hzero⟩ := exists_zero_of_strict_descent
    (fun candidate ↦ candidate.strongFiveDefect χ)
    (fun candidate ↦ n ≤ 2 * (candidate.support χ).card)
    initial hinitial (fun current hcurrent hpositive ↦ by
      obtain ⟨improved, _hnear, himproved, hlower⟩ :=
        hdescent hreal hfree current hcurrent hpositive
      exact ⟨improved, himproved, hlower⟩)
  exact ⟨classifier,
    (AmbientTwoCellClassifier.strongFiveDefect_eq_zero_iff χ classifier).mp hzero,
    hhalf⟩

/-- The local-descent producer feeds the existing unrestricted recurrence
interface without a same-`k` upper-bound premise. -/
theorem predecessorHalfSubsetAt_six_of_ambientTwoCellDefectDescent
    {radius : ℕ} (hdescent : AmbientTwoCellDefectDescentAtSix radius) :
    PredecessorHalfSubsetAt 6 := by
  intro n χ hreal hfree
  obtain ⟨classifier, hsupportFree, hhalf⟩ :=
    ambientDownsetTwoCellBooleanHalfSupportAtSix_of_defectDescent hdescent hreal hfree
  exact ⟨classifier.support χ, by simpa using hsupportFree, hhalf⟩

end ErdosSzekeres

end
