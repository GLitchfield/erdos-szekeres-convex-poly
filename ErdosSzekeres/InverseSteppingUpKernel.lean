module

public import ErdosSzekeres.Decomposable
public import ErdosSzekeres.StrongPredecessorBicoloring

@[expose] public section

/-!
# Inverse stepping-up kernel

A pure predecessor family on one side of a deep-below split is impossible in
a target-free coloring once the opposite side is nonempty: one opposite
singleton glues the pure cup/cap to the forbidden next strong polygon.  This
is the local, noncircular part of a possible inverse-composition producer.
-/

namespace ErdosSzekeres

/-- If every strong predecessor on the lower side is a cup, then the lower
side is predecessor-free in a target-free deep split. -/
theorem HasDeepBelowSplit.predecessorFree_lower_of_cupPure
    {n k : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hk : 1 ≤ k)
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hupper : upper.Nonempty)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ k)
    (hpure : ∀ polygon : Finset (Fin n),
      polygon ⊆ lower → polygon.card = k - 1 →
        IsStrongPolygonSet χ polygon → IsCupSet χ polygon) :
    ¬ContainsStrongPolygonSet χ lower (k - 1) := by
  rintro ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩
  obtain ⟨q, hqUpper⟩ := hupper
  have hsingletonSub : ({q} : Finset (Fin n)) ⊆ upper := by
    simp [hqUpper]
  have hsingletonCap : IsCapSet χ ({q} : Finset (Fin n)) := by
    intro t hi hj hk'
    simp only [Finset.mem_singleton] at hi hj hk'
    exact ((ne_of_lt t.hij) (hi.trans hj.symm)).elim
  have htarget := hsplit.containsStrongPolygonSet_of_cup_cap
    hpolygonSub hsingletonSub
    (hpure polygon hpolygonSub hpolygonCard hpolygonStrong)
    hsingletonCap (k := k) (by simp [hpolygonCard]; omega)
  exact hnoStrong
    (FinsetPolygon.ContainsStrongPolygonSet.mono htarget (by
      intro x _hx
      exact Finset.mem_univ x))

/-- Color-dual local kernel for a pure cap family on the upper side. -/
theorem HasDeepBelowSplit.predecessorFree_upper_of_capPure
    {n k : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hk : 1 ≤ k)
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hlower : lower.Nonempty)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ k)
    (hpure : ∀ polygon : Finset (Fin n),
      polygon ⊆ upper → polygon.card = k - 1 →
        IsStrongPolygonSet χ polygon → IsCapSet χ polygon) :
    ¬ContainsStrongPolygonSet χ upper (k - 1) := by
  rintro ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩
  obtain ⟨q, hqLower⟩ := hlower
  have hsingletonSub : ({q} : Finset (Fin n)) ⊆ lower := by
    simp [hqLower]
  have hsingletonCup : IsCupSet χ ({q} : Finset (Fin n)) := by
    intro t hi hj hk'
    simp only [Finset.mem_singleton] at hi hj hk'
    exact ((ne_of_lt t.hij) (hi.trans hj.symm)).elim
  have htarget := hsplit.containsStrongPolygonSet_of_cup_cap
    hsingletonSub hpolygonSub hsingletonCup
    (hpure polygon hpolygonSub hpolygonCard hpolygonStrong)
    (k := k) (by simp [hpolygonCard]; omega)
  exact hnoStrong
    (FinsetPolygon.ContainsStrongPolygonSet.mono htarget (by
      intro x _hx
      exact Finset.mem_univ x))

/-- A half-sized pure side of a deep split.  This producer mentions neither
the exact power-of-two threshold nor the desired upper theorem. -/
def HalfPureDeepSplitAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ lower upper : Finset (Fin n),
      HasDeepBelowSplit χ lower upper ∧
      ((upper.Nonempty ∧ n ≤ 2 * lower.card ∧
          ∀ polygon : Finset (Fin n),
            polygon ⊆ lower → polygon.card = k - 1 →
              IsStrongPolygonSet χ polygon → IsCupSet χ polygon) ∨
       (lower.Nonempty ∧ n ≤ 2 * upper.card ∧
          ∀ polygon : Finset (Fin n),
            polygon ⊆ upper → polygon.card = k - 1 →
              IsStrongPolygonSet χ polygon → IsCapSet χ polygon))

/-- The pure deep-split producer feeds the already compiled half-subset
recurrence interface. -/
theorem predecessorHalfSubsetAt_of_halfPureDeepSplit
    {k : ℕ} (hk : 1 ≤ k) (hpure : HalfPureDeepSplitAt k) :
    PredecessorHalfSubsetAt k := by
  intro n χ hrealizable hnoStrong
  obtain ⟨lower, upper, hsplit, hlower | hupper⟩ :=
    hpure hrealizable hnoStrong
  · exact ⟨lower,
      hsplit.predecessorFree_lower_of_cupPure hk hlower.1 hnoStrong hlower.2.2,
      hlower.2.1⟩
  · exact ⟨upper,
      hsplit.predecessorFree_upper_of_capPure hk hupper.1 hnoStrong hupper.2.2,
      hupper.2.1⟩

end ErdosSzekeres
