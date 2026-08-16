module

public import ErdosSzekeres.SukRegionChainGeometry

@[expose] public section

/-!
# The source-faithful adjacent-pool recurrence in Suk's argument

This module proves the exact one-pool base and adjacent-pool carry/completion
step.  The public recurrence derives the raw geometry and total order of the
right pool from `SukAdjacentChainPools` and uses the existing adjacent-region
certificate consumer in its completion branch.
-/

namespace ErdosSzekeres

noncomputable section

/-- The one-pool threshold has both the recurrence form and Suk's symmetric
binomial form. -/
theorem sukAdjacentPool_choose_threshold
    (n K a : ℕ) (ha : a ≤ n) (hdeficit : 2 ≤ n - a) (hcarry : 2 ≤ a + K) :
    Nat.choose ((n - a) + (a + K) - 4) ((n - a) - 2) =
        Nat.choose (n + K - 4) (n - a - 2) ∧
      Nat.choose (n + K - 4) (n - a - 2) =
        Nat.choose (n + K - 4) (a + K - 2) := by
  have htop : (n - a) + (a + K) - 4 = n + K - 4 := by omega
  constructor
  · rw [htop]
  · exact Nat.choose_symm_of_eq_add (by omega)

/-- Adding a positive cap increment strictly decreases the remaining deficit. -/
theorem sukAdjacentPool_deficit_lt
    (n K a : ℕ) (hK : 0 < K) (hdeficit : 2 ≤ n - a) :
    n - (a + K) < n - a := by
  omega

/-- Raw one-region geometry yields either an unanchored `n`-point convex
subset or a full left-anchor cap of size `K`. -/
theorem sukRegionGeometry_base_fullAnchoredCap
    (outerLeft rightAnchor leftAnchor outerRight : Point 2)
    (s : Finset (Point 2))
    (hgeometry : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (hchain : ∀ {p : Point 2}, p ∈ s →
      ∀ {q : Point 2}, q ∈ s → p ≠ q →
      SukRegionLE outerLeft outerRight p q ∨
        SukRegionLE outerLeft outerRight q p)
    (n K : ℕ) (hn : 2 ≤ n) (hK : 2 ≤ K)
    (hcard : Nat.choose (n + K - 4) (n - 2) < s.card) :
    ContainsConvexSubset s n ∨
      SukRegionHasFullAnchoredCap leftAnchor s K := by
  rcases sukRegionGeometry_to_fullAnchoredCap
      outerLeft rightAnchor leftAnchor outerRight s hgeometry hchain
      n K hn hK hcard with hright | hleft
  · left
    rcases hright with ⟨selected, hselectedSubset, hselectedCard, hanchored⟩
    exact ⟨selected, hselectedSubset, hselectedCard,
      hanchored.mono (Finset.subset_insert rightAnchor selected)⟩
  · exact Or.inr hleft

/-- Suk's adjacent-pool recurrence: a right-anchor cap completes the carried
left cap, while a left-anchor cap is the strictly advanced state for the next
window. -/
theorem sukAdjacentPool_fullCapStep
    (x0 x1 x2 x3 x4 : Point 2)
    (leftPool rightPool : Finset (Point 2))
    (n K a : ℕ)
    (hpools : SukAdjacentChainPools
      x0 x1 x2 x3 x4 leftPool rightPool)
    (hleft : SukRegionHasFullAnchoredCap x2 leftPool a)
    (ha : a ≤ n) (hK : 0 < K)
    (hdeficit : 2 ≤ n - a) (hcarry : 2 ≤ a + K)
    (hcard : Nat.choose (n + K - 4) (n - a - 2) < rightPool.card) :
    ContainsConvexSubset (leftPool ∪ rightPool) n ∨
      SukRegionHasFullAnchoredCap x3 rightPool (a + K) := by
  have hstrictDeficit : n - (a + K) < n - a :=
    sukAdjacentPool_deficit_lt n K a hK hdeficit
  let hrightGeometry : SukRegionGeometry x1 x2 x3 x4 rightPool := {
    anchorsCap := hpools.anchorsCap.rightFour
    generalPosition := by
      apply hpools.generalPosition.mono
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_union] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl | hp
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))
    region := by
      intro p hp
      exact hpools.rightRegion hp
  }
  have hthreshold :=
    (sukAdjacentPool_choose_threshold n K a ha hdeficit hcarry).1
  have hcardRaw :
      Nat.choose ((n - a) + (a + K) - 4) ((n - a) - 2) < rightPool.card := by
    rw [hthreshold]
    exact hcard
  have halt := sukRegionGeometry_to_fullAnchoredCap
    x1 x2 x3 x4 rightPool hrightGeometry
    (by
      intro p hp q hq hpq
      exact hpools.rightChain hp hq hpq)
    (n - a) (a + K) hdeficit hcarry hcardRaw
  rcases halt with hright | hright
  · rcases hleft with
      ⟨left, hleftSubset, hleftCard, hleftConvex⟩
    rcases hright with
      ⟨right, hrightSubset, hrightCard, hrightConvex⟩
    have hselection : SukGlobalAdjacentChainSelection
        x2 leftPool rightPool a (n - a) :=
      ⟨left, right, hleftSubset, hrightSubset,
        hleftCard, hrightCard, hleftConvex, hrightConvex⟩
    obtain ⟨selectedLeft, selectedRight,
        hselectedLeftSubset, hselectedRightSubset,
        hselectedLeftCard, hselectedRightCard,
        hcertificate, hselectedConvex⟩ :=
      sukGlobalAdjacentChainSelection_toCertificate
        x0 x1 x2 x3 x4 leftPool rightPool a (n - a) hpools hselection
    left
    refine ⟨selectedLeft ∪ selectedRight, ?_, ?_, hselectedConvex⟩
    · intro p hp
      simp only [Finset.mem_union] at hp ⊢
      exact hp.elim (fun h ↦ Or.inl (hselectedLeftSubset h))
        (fun h ↦ Or.inr (hselectedRightSubset h))
    · rw [Finset.card_union_of_disjoint hcertificate.disjoint,
        hselectedLeftCard, hselectedRightCard]
      omega
  · exact (And.intro hstrictDeficit (Or.inr hright)).2

end

end ErdosSzekeres

end
