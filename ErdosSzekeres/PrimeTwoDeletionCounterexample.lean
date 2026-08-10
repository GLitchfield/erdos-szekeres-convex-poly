module

public import ErdosSzekeres.DecompositionPrime
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# A realizable obstruction to prime one-or-two deletion

This file kernel-checks an integer-coordinate seven-point configuration that
is decomposition-prime and strong-six-free, but has no prime restriction after
deleting one or two vertices. It refutes the proposed Layer-F prime-deletion
descent before any pin-coding argument.
-/

namespace ErdosSzekeres
namespace PrimeTwoDeletionCounterexample

def deepBelowSplitBool {n : ℕ} (χ : TripleColoring n)
    (lower upper : Finset (Fin n)) : Bool :=
  decide (Disjoint lower upper) &&
    (List.finRange n).all fun i ↦
      (List.finRange n).all fun j ↦
        (List.finRange n).all fun k ↦
          if hij : i < j then
            if hjk : j < k then
              if _hi : i ∈ lower ∪ upper then
                if _hj : j ∈ lower ∪ upper then
                  if _hk : k ∈ lower ∪ upper then
                    if _hallLower : i ∈ lower ∧ j ∈ lower ∧ k ∈ lower then
                      true
                    else if _hallUpper : i ∈ upper ∧ j ∈ upper ∧ k ∈ upper then
                      true
                    else decide (χ ⟨i, j, k, hij, hjk⟩ =
                      if j ∈ lower then Turn.left else Turn.right)
                  else true
                else true
              else true
            else true
          else true

theorem deepBelowSplitBool_eq_true_iff {n : ℕ} (χ : TripleColoring n)
    (lower upper : Finset (Fin n)) :
    deepBelowSplitBool χ lower upper = true ↔
      HasDeepBelowSplit χ lower upper := by
  constructor
  · intro h
    have hand : decide (Disjoint lower upper) = true ∧
        ((List.finRange n).all fun i ↦
          (List.finRange n).all fun j ↦
            (List.finRange n).all fun k ↦
              if hij : i < j then
                if hjk : j < k then
                  if hi : i ∈ lower ∪ upper then
                    if hj : j ∈ lower ∪ upper then
                      if hk : k ∈ lower ∪ upper then
                        if hallLower : i ∈ lower ∧ j ∈ lower ∧ k ∈ lower then
                          true
                        else if hallUpper :
                            i ∈ upper ∧ j ∈ upper ∧ k ∈ upper then
                          true
                        else decide (χ ⟨i, j, k, hij, hjk⟩ =
                          if j ∈ lower then Turn.left else Turn.right)
                      else true
                    else true
                  else true
                else true
              else true) = true := by
      simpa only [deepBelowSplitBool, Bool.and_eq_true] using h
    refine ⟨of_decide_eq_true hand.1, ?_⟩
    intro t hi hj hk hnotLower hnotUpper
    have hiCheck := (List.all_eq_true.mp hand.2) t.i (List.mem_finRange t.i)
    have hjCheck := (List.all_eq_true.mp hiCheck) t.j (List.mem_finRange t.j)
    have hkCheck := (List.all_eq_true.mp hjCheck) t.k (List.mem_finRange t.k)
    simpa [t.hij, t.hjk, hi, hj, hk, hnotLower, hnotUpper] using hkCheck
  · intro h
    have hdisjoint : decide (Disjoint lower upper) = true := decide_eq_true h.disjoint
    have hall : ((List.finRange n).all fun i ↦
        (List.finRange n).all fun j ↦
          (List.finRange n).all fun k ↦
            if hij : i < j then
              if hjk : j < k then
                if hi : i ∈ lower ∪ upper then
                  if hj : j ∈ lower ∪ upper then
                    if hk : k ∈ lower ∪ upper then
                      if hallLower : i ∈ lower ∧ j ∈ lower ∧ k ∈ lower then
                        true
                      else if hallUpper : i ∈ upper ∧ j ∈ upper ∧ k ∈ upper then
                        true
                      else decide (χ ⟨i, j, k, hij, hjk⟩ =
                        if j ∈ lower then Turn.left else Turn.right)
                    else true
                  else true
                else true
              else true
            else true) = true := by
      apply List.all_eq_true.mpr
      intro i _hi
      apply List.all_eq_true.mpr
      intro j _hj
      apply List.all_eq_true.mpr
      intro k _hk
      by_cases hij : i < j
      · by_cases hjk : j < k
        · by_cases hi : i ∈ lower ∪ upper
          · by_cases hj : j ∈ lower ∪ upper
            · by_cases hk : k ∈ lower ∪ upper
              · by_cases hallLower : i ∈ lower ∧ j ∈ lower ∧ k ∈ lower
                · simp [hij, hjk, hi, hj, hk, hallLower]
                · by_cases hallUpper : i ∈ upper ∧ j ∈ upper ∧ k ∈ upper
                  · simp [hij, hjk, hi, hj, hk, hallLower, hallUpper]
                  · simp [hij, hjk, hi, hj, hk, hallLower, hallUpper,
                      h.crossing ⟨i, j, k, hij, hjk⟩ hi hj hk
                        hallLower hallUpper]
              · simp [hij, hjk, hi, hj, hk]
            · simp [hij, hjk, hi, hj]
          · simp [hij, hjk, hi]
        · simp [hij, hjk]
      · simp [hij]
    simpa only [deepBelowSplitBool, Bool.and_eq_true] using
      And.intro hdisjoint hall

local instance decidableHasDeepBelowSplit {n : ℕ} (χ : TripleColoring n)
    (lower upper : Finset (Fin n)) : Decidable (HasDeepBelowSplit χ lower upper) :=
  decidable_of_iff (deepBelowSplitBool χ lower upper = true)
    (deepBelowSplitBool_eq_true_iff χ lower upper)

local instance decidableHasProperDeepBelowSplitOn {n : ℕ} (χ : TripleColoring n)
    (support : Finset (Fin n)) : Decidable (HasProperDeepBelowSplitOn χ support) := by
  unfold HasProperDeepBelowSplitOn
  infer_instance

local instance decidableIsDecompositionPrimeOn {n : ℕ} (χ : TripleColoring n)
    (support : Finset (Fin n)) : Decidable (IsDecompositionPrimeOn χ support) := by
  unfold IsDecompositionPrimeOn
  infer_instance

def leftCodes : List ℕ := [
  35, 36, 45, 46, 56, 126, 134, 135, 136, 145,
  146, 156, 234, 235, 236, 245, 246, 256, 345, 346]

def color : TripleColoring 7 := fun t ↦
  if 100 * t.i.val + 10 * t.j.val + t.k.val ∈ leftCodes then
    Turn.left
  else
    Turn.right

noncomputable section

def points : Fin 7 → Point 2 := ![
  ![0, 0],
  ![1, 0],
  ![2, -6],
  ![3, -54],
  ![4, -74],
  ![5, -30],
  ![6, -21]]

set_option maxHeartbeats 4000000 in
noncomputable def configuration : SweptConfiguration 7 where
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

set_option maxHeartbeats 4000000 in
theorem configuration_coloring : configuration.tripleColoring = color := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [configuration, points,
    SweptConfiguration.tripleColoring, SweptConfiguration.turn,
    color, leftCodes, orientation]

theorem color_sweepRealizable : IsSweepRealizable color :=
  ⟨configuration, configuration_coloring⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem color_prime : IsDecompositionPrimeOn color Finset.univ := by
  decide

set_option maxRecDepth 100000 in
theorem color_noStrongSetBool_six :
    ∀ s : Finset (Fin 7), s.card = 6 →
      RankProfileCollision.strongPolygonSetBool color s = false := by
  decide

set_option maxRecDepth 100000 in
theorem color_noStrongSix :
    ¬ContainsStrongPolygonSet color Finset.univ 6 := by
  rintro ⟨polygon, _hsub, hcard, hstrong⟩
  have htrue :=
    (RankProfileCollision.strongPolygonSetBool_eq_true_iff color polygon).2
      hstrong
  rw [color_noStrongSetBool_six polygon hcard] at htrue
  contradiction

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem color_no_prime_after_one_or_two_deletions :
    ∀ deleted : Finset (Fin 7), deleted.card = 1 ∨ deleted.card = 2 →
      ¬IsDecompositionPrimeOn color (Finset.univ \ deleted) := by
  decide

/-- The proposed Layer-F descent contract at the first nontrivial target. -/
def PrimeTwoDeletionOrTargetAtSix : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)},
    IsSweepRealizable χ → IsDecompositionPrimeOn χ support →
    6 < support.card →
    ¬ContainsStrongPolygonSet χ support 6 →
    ∃ subset, subset ⊂ support ∧ support.card ≤ subset.card + 2 ∧
      IsDecompositionPrimeOn χ subset

/-- The exact rational seven-point coloring refutes one-or-two deletion
descent for target-free decomposition-prime supports. -/
theorem not_primeTwoDeletionOrTargetAtSix :
    ¬PrimeTwoDeletionOrTargetAtSix := by
  intro hdescent
  obtain ⟨subset, hproper, hnear, hprime⟩ :=
    hdescent color_sweepRealizable color_prime (by decide) color_noStrongSix
  have hsubset : subset ⊆ Finset.univ := Finset.subset_univ subset
  have hsubsetCard : subset.card < 7 := by
    have := Finset.card_lt_card hproper
    simpa using this
  let deleted : Finset (Fin 7) := Finset.univ \ subset
  have hdeletedCard : deleted.card = 1 ∨ deleted.card = 2 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hsubset
    dsimp [deleted] at hcard
    simp only [Finset.card_univ, Fintype.card_fin] at hcard hnear
    change (Finset.univ \ subset).card = 1 ∨
      (Finset.univ \ subset).card = 2
    have hpositive : 1 ≤ (Finset.univ \ subset).card := by omega
    have hsmall : (Finset.univ \ subset).card ≤ 2 := by omega
    by_cases hone : (Finset.univ \ subset).card ≤ 1
    · left
      omega
    · right
      omega
  apply color_no_prime_after_one_or_two_deletions deleted hdeletedCard
  have hrecover : Finset.univ \ deleted = subset := by
    ext x
    simp [deleted]
  rwa [hrecover]

/-- A sweep-realizable decomposition-prime seven-point coloring without a
strong six has no prime subconfiguration after deleting one or two points. -/
theorem primeTwoDeletion_counterexample :
    IsSweepRealizable color ∧
      IsDecompositionPrimeOn color Finset.univ ∧
      ¬ContainsStrongPolygonSet color Finset.univ 6 ∧
      ∀ deleted : Finset (Fin 7), deleted.card = 1 ∨ deleted.card = 2 →
        ¬IsDecompositionPrimeOn color (Finset.univ \ deleted) :=
  ⟨color_sweepRealizable, color_prime, color_noStrongSix,
    color_no_prime_after_one_or_two_deletions⟩

end

end PrimeTwoDeletionCounterexample
end ErdosSzekeres

end
