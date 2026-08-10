module

public import ErdosSzekeres.StructuralChargingRootCritical

@[expose] public section

/-!
# Color duality for decomposable E3 states

Reflection of the truncated binomial window sends the index `j` to
`k - 2 - j`.  Consequently the proposed threshold is symmetric in its cup
and cap parameters.  Color duality then turns every hereditary state proof at
`(a, u, k)` into one at `(u, a, k)`.
-/

namespace ErdosSzekeres

/-- The truncated binomial window is symmetric in its cap and cup parameters. -/
theorem decomposableBinomialWindow_comm
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    decomposableBinomialWindow a u k =
      decomposableBinomialWindow u a k := by
  unfold decomposableBinomialWindow
  apply Finset.sum_nbij' (fun j ↦ k - 2 - j) (fun j ↦ k - 2 - j)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    exact (Nat.choose_symm (by omega)).symm

/-- The proposed decomposable threshold is symmetric in its cap and cup
parameters throughout the range used by E3. -/
theorem decomposableThreshold_comm
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    decomposableThreshold a u k = decomposableThreshold u a k := by
  rw [decomposableThreshold, decomposableThreshold]
  simp only [show ¬(a = 1 ∨ u = 1) by omega,
    show ¬(u = 1 ∨ a = 1) by omega, ↓reduceIte]
  by_cases hbase : a + u ≤ k + 3
  · rw [if_pos hbase, if_pos (by omega)]
    simpa [add_comm] using Nat.choose_symm_of_eq_add
      (n := a + u - 4) (a := a - 2) (b := u - 2) (by omega)
  · rw [if_neg hbase, if_neg (by omega)]
    exact decomposableBinomialWindow_comm ha hu hak huk

/-- Color duality transports a hereditary E3 state across the diagonal. -/
theorem decomposableStateUpper_comm
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hstate : DecomposableStateUpper a u k) :
    DecomposableStateUpper u a k := by
  intro n χ s hdecomposable hcard
  have hcard' : decomposableThreshold a u k < s.card := by
    rw [decomposableThreshold_comm ha hu hak huk]
    exact hcard
  rcases hstate hdecomposable.dual hcard' with hcap | hcup | hstrong
  · exact Or.inr (Or.inl (containsCapSet_dual_iff.mp hcap))
  · exact Or.inl (containsCupSet_dual_iff.mp hcup)
  · exact Or.inr (Or.inr (containsStrongPolygonSet_dual_iff.mp hstrong))

/-- The hereditary E3 states at `(a, u, k)` and `(u, a, k)` are equivalent. -/
theorem decomposableStateUpper_comm_iff
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    DecomposableStateUpper a u k ↔ DecomposableStateUpper u a k := by
  constructor
  · exact decomposableStateUpper_comm ha hu hak huk
  · exact decomposableStateUpper_comm hu ha huk hak

/-- Color duality transports the exact root-local E3 transition across the
parameter diagonal.  The deep-below children exchange roles under duality. -/
theorem decomposableRootTransitionUpper_comm
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hroot : DecomposableRootTransitionUpper a u k) :
    DecomposableRootTransitionUpper u a k := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hnoCap hnoCup hnoStrong
  have hlowerBound' : lower.card ≤ decomposableThreshold a u k := by
    rw [decomposableThreshold_comm ha hu hak huk]
    exact hlowerBound
  have hupperBound' : upper.card ≤ decomposableThreshold a u k := by
    rw [decomposableThreshold_comm ha hu hak huk]
    exact hupperBound
  have hbound := hroot hupper.dual hlower.dual hdeep.dual
    hupperBound' hlowerBound'
    (fun hcap ↦ hnoCup (by
      simpa [Finset.union_comm] using containsCapSet_dual_iff.mp hcap))
    (fun hcup ↦ hnoCap (by
      simpa [Finset.union_comm] using containsCupSet_dual_iff.mp hcup))
    (fun hstrong ↦ hnoStrong (by
      simpa [Finset.union_comm] using
        containsStrongPolygonSet_dual_iff.mp hstrong))
  rw [← decomposableThreshold_comm ha hu hak huk]
  simpa [Finset.union_comm] using hbound

/-- The two color-dual root-local transitions are equivalent. -/
theorem decomposableRootTransitionUpper_comm_iff
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    DecomposableRootTransitionUpper a u k ↔
      DecomposableRootTransitionUpper u a k := by
  constructor
  · exact decomposableRootTransitionUpper_comm ha hu hak huk
  · exact decomposableRootTransitionUpper_comm hu ha huk hak

/-- Exact critical-root impossibility is likewise symmetric under color
duality. -/
theorem decomposableCriticalRootImpossible_comm
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hcritical : DecomposableCriticalRootImpossible a u k) :
    DecomposableCriticalRootImpossible u a k := by
  apply rootTransitionUpper_implies_criticalRootImpossible
  apply decomposableRootTransitionUpper_comm ha hu hak huk
  exact criticalRootImpossible_implies_rootTransitionUpper hcritical

/-- The two color-dual exact critical-root obstructions are equivalent. -/
theorem decomposableCriticalRootImpossible_comm_iff
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    DecomposableCriticalRootImpossible a u k ↔
      DecomposableCriticalRootImpossible u a k := by
  constructor
  · exact decomposableCriticalRootImpossible_comm ha hu hak huk
  · exact decomposableCriticalRootImpossible_comm hu ha huk hak

end ErdosSzekeres
