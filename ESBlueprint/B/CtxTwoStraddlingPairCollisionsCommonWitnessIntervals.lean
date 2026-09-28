import ESBlueprint.B.CtxPureExtensionsPositionMonotone

namespace ErdosSzekeres

/-- Two distinct ordered-rank collisions, each witnessed across the same marker orientation, admit a common pair of original source intervals whose endpoints are chosen from the four witnesses; both collision coordinates and hence two distinct ranks lie in both intervals.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_pure_extensions_position_monotone
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem CtxTwoStraddlingPairCollisionsCommonWitnessIntervals (σ : Ctx.Context) (t : Ctx.Side) (G y : ℕ) (z w : ℕ × ℕ) (lowZ highZ lowW highW : ℕ) (hzw : z ≠ w) : let I : ℕ → Finset ℕ := fun q => Finset.Icc (σ.leftExt t 0 q + 1) (G - 1 - σ.rightExt t 0 q); z.1 ∈ I lowZ → z.2 ∈ I lowZ → z.1 ∈ I highZ → z.2 ∈ I highZ → w.1 ∈ I lowW → w.2 ∈ I lowW → w.1 ∈ I highW → w.2 ∈ I highW → ((lowZ < y ∧ y < highZ ∧ lowW < y ∧ y < highW) ∨ (highZ < y ∧ y < lowZ ∧ highW < y ∧ y < lowW)) → ∃ low high, (low = lowZ ∨ low = lowW) ∧ (high = highZ ∨ high = highW) ∧ ((low < y ∧ y < high) ∨ (high < y ∧ y < low)) ∧ z.1 ∈ I low ∧ z.2 ∈ I low ∧ z.1 ∈ I high ∧ z.2 ∈ I high ∧ w.1 ∈ I low ∧ w.2 ∈ I low ∧ w.1 ∈ I high ∧ w.2 ∈ I high ∧ ∃ r r', r ≠ r' ∧ r ∈ I low ∧ r ∈ I high ∧ r' ∈ I low ∧ r' ∈ I high := by
  classical
  dsimp only
  intro hz1Low hz2Low hz1High hz2High
    hw1Low hw2Low hw1High hw2High hsep
  have hbetween (a b c r : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
      (ha : r ∈ Finset.Icc (σ.leftExt t 0 a + 1)
        (G - 1 - σ.rightExt t 0 a))
      (hc : r ∈ Finset.Icc (σ.leftExt t 0 c + 1)
        (G - 1 - σ.rightExt t 0 c)) :
      r ∈ Finset.Icc (σ.leftExt t 0 b + 1)
        (G - 1 - σ.rightExt t 0 b) := by
    have hmAB := ctx_pure_extensions_position_monotone σ t 0 a b hab
    have hmBC := ctx_pure_extensions_position_monotone σ t 0 b c hbc
    simp only [Finset.mem_Icc] at ha hc ⊢
    constructor <;> omega
  rcases hsep with hforward | hreverse
  · rcases hforward with ⟨hlZ, hZh, hlW, hWh⟩
    let low := max lowZ lowW
    let high := min highZ highW
    have hlowZ : lowZ ≤ low := by
      exact Nat.le_max_left _ _
    have hlowW : lowW ≤ low := by
      exact Nat.le_max_right _ _
    have hlowHighZ : low ≤ highZ := by
      apply Nat.max_le.mpr
      omega
    have hlowHighW : low ≤ highW := by
      apply Nat.max_le.mpr
      omega
    have hlowZHigh : lowZ ≤ high := by
      apply Nat.le_min.mpr
      omega
    have hlowWHigh : lowW ≤ high := by
      apply Nat.le_min.mpr
      omega
    have hhighZ : high ≤ highZ := by
      exact Nat.min_le_left _ _
    have hhighW : high ≤ highW := by
      exact Nat.min_le_right _ _
    have hlowBelow : low < y := by
      have hle : low ≤ y - 1 := by
        apply Nat.max_le.mpr
        omega
      omega
    have hhighAbove : y < high := by
      have hle : y + 1 ≤ high := by
        apply Nat.le_min.mpr
        omega
      omega
    have hlowChoice : low = lowZ ∨ low = lowW := by
      by_cases h : lowZ ≤ lowW
      · right
        exact Nat.max_eq_right h
      · left
        exact Nat.max_eq_left (by omega)
    have hhighChoice : high = highZ ∨ high = highW := by
      by_cases h : highZ ≤ highW
      · left
        exact Nat.min_eq_left h
      · right
        exact Nat.min_eq_right (by omega)
    have hz1Low' := hbetween lowZ low highZ z.1 hlowZ hlowHighZ
      hz1Low hz1High
    have hz2Low' := hbetween lowZ low highZ z.2 hlowZ hlowHighZ
      hz2Low hz2High
    have hz1High' := hbetween lowZ high highZ z.1 hlowZHigh hhighZ
      hz1Low hz1High
    have hz2High' := hbetween lowZ high highZ z.2 hlowZHigh hhighZ
      hz2Low hz2High
    have hw1Low' := hbetween lowW low highW w.1 hlowW hlowHighW
      hw1Low hw1High
    have hw2Low' := hbetween lowW low highW w.2 hlowW hlowHighW
      hw2Low hw2High
    have hw1High' := hbetween lowW high highW w.1 hlowWHigh hhighW
      hw1Low hw1High
    have hw2High' := hbetween lowW high highW w.2 hlowWHigh hhighW
      hw2Low hw2High
    refine ⟨low, high, hlowChoice, hhighChoice,
      Or.inl ⟨hlowBelow, hhighAbove⟩,
      hz1Low', hz2Low', hz1High', hz2High',
      hw1Low', hw2Low', hw1High', hw2High', ?_⟩
    by_cases hfirst : z.1 = w.1
    · have hsecond : z.2 ≠ w.2 := by
        intro hs
        apply hzw
        exact Prod.ext hfirst hs
      exact ⟨z.2, w.2, hsecond,
        hz2Low', hz2High', hw2Low', hw2High'⟩
    · exact ⟨z.1, w.1, hfirst,
        hz1Low', hz1High', hw1Low', hw1High'⟩
  · rcases hreverse with ⟨hhZ, hZl, hhW, hWl⟩
    let low := min lowZ lowW
    let high := max highZ highW
    have hhighZ : highZ ≤ high := by
      exact Nat.le_max_left _ _
    have hhighW : highW ≤ high := by
      exact Nat.le_max_right _ _
    have hhighLowZ : high ≤ lowZ := by
      apply Nat.max_le.mpr
      omega
    have hhighLowW : high ≤ lowW := by
      apply Nat.max_le.mpr
      omega
    have hhighZLow : highZ ≤ low := by
      apply Nat.le_min.mpr
      omega
    have hhighWLow : highW ≤ low := by
      apply Nat.le_min.mpr
      omega
    have hlowZ : low ≤ lowZ := by
      exact Nat.min_le_left _ _
    have hlowW : low ≤ lowW := by
      exact Nat.min_le_right _ _
    have hhighBelow : high < y := by
      have hle : high ≤ y - 1 := by
        apply Nat.max_le.mpr
        omega
      omega
    have hlowAbove : y < low := by
      have hle : y + 1 ≤ low := by
        apply Nat.le_min.mpr
        omega
      omega
    have hlowChoice : low = lowZ ∨ low = lowW := by
      by_cases h : lowZ ≤ lowW
      · left
        exact Nat.min_eq_left h
      · right
        exact Nat.min_eq_right (by omega)
    have hhighChoice : high = highZ ∨ high = highW := by
      by_cases h : highZ ≤ highW
      · right
        exact Nat.max_eq_right h
      · left
        exact Nat.max_eq_left (by omega)
    have hz1Low' := hbetween highZ low lowZ z.1 hhighZLow hlowZ
      hz1High hz1Low
    have hz2Low' := hbetween highZ low lowZ z.2 hhighZLow hlowZ
      hz2High hz2Low
    have hz1High' := hbetween highZ high lowZ z.1 hhighZ hhighLowZ
      hz1High hz1Low
    have hz2High' := hbetween highZ high lowZ z.2 hhighZ hhighLowZ
      hz2High hz2Low
    have hw1Low' := hbetween highW low lowW w.1 hhighWLow hlowW
      hw1High hw1Low
    have hw2Low' := hbetween highW low lowW w.2 hhighWLow hlowW
      hw2High hw2Low
    have hw1High' := hbetween highW high lowW w.1 hhighW hhighLowW
      hw1High hw1Low
    have hw2High' := hbetween highW high lowW w.2 hhighW hhighLowW
      hw2High hw2Low
    refine ⟨low, high, hlowChoice, hhighChoice,
      Or.inr ⟨hhighBelow, hlowAbove⟩,
      hz1Low', hz2Low', hz1High', hz2High',
      hw1Low', hw2Low', hw1High', hw2High', ?_⟩
    by_cases hfirst : z.1 = w.1
    · have hsecond : z.2 ≠ w.2 := by
        intro hs
        apply hzw
        exact Prod.ext hfirst hs
      exact ⟨z.2, w.2, hsecond,
        hz2Low', hz2High', hw2Low', hw2High'⟩
    · exact ⟨z.1, w.1, hfirst,
        hz1Low', hz1High', hw1Low', hw1High'⟩

end ErdosSzekeres
