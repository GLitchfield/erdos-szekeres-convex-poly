module

public import ErdosSzekeres.SukConsecutiveDilworth
public import ErdosSzekeres.SukChainRichIteration

@[expose] public section

/-!
# The consecutive-chain branch of the global Suk split

This module maps the actual subtype chains supplied by the global Dilworth
split back to point pools, restricts the raw geometry to their consecutive
interval, and invokes the indexed adjacent-pool recurrence.
-/

namespace ErdosSzekeres

noncomputable section

/-- The chain-run branch of the raw-pool split yields a convex subset; the
unchanged alternative retains the actual nonadjacent antichain witnesses. -/
theorem SukConsecutiveRawPools.containsConvexSubset_or_antichainPacking
    {L chainSize antiSize t m n K : ℕ}
    {anchors : ℕ → Point 2}
    {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (hchainSize : 1 ≤ chainSize) (hantiSize : 1 ≤ antiSize)
    (ht : 1 ≤ t) (hm : 2 ≤ m)
    (hL : (2 * t - 1) * m ≤ L)
    (hpoolCard : ∀ i, i < L →
      (chainSize - 1) * (antiSize - 1) < (pools i).card)
    (hK : 2 ≤ K)
    (hfinalDeficit : 2 ≤ n - ((m - 1) * K))
    (hfinalSize : n ≤ m * K)
    (hchainCard : ∀ u, u < m →
      Nat.choose (n + K - 4) ((u + 1) * K - 2) < chainSize) :
    ContainsConvexSubset (SukConsecutivePoolCarrier L pools) n ∨
      ∃ selected : Finset (Fin L),
        selected.card = t ∧ PairwiseNonadjacent selected ∧
          ∀ i, i ∈ selected →
            SukRegionHasAntichainSubset
              (anchors i.val) (anchors (i.val + 3))
              (pools i.val) antiSize := by
  classical
  rcases hraw.chainRun_or_antichainPacking
      hchainSize hantiSize ht (by omega) hL hpoolCard with hanti | hrun
  · exact Or.inr hanti
  · rcases hrun with ⟨start, hstart, hchains⟩
    let chainWitness : (u : Fin m) →
        Finset (↥(pools (start + u.val))) :=
      fun u ↦ (hchains u).choose
    have chainWitnessCard (u : Fin m) :
        chainSize ≤ (chainWitness u).card := by
      simpa [chainWitness] using (hchains u).choose_spec.1
    have chainWitnessIsChain (u : Fin m) :
        IsChain
          (fun p q : ↥(pools (start + u.val)) ↦
            SukRegionLE
              (anchors (start + u.val))
              (anchors (start + u.val + 3)) p.1 q.1)
          (↑(chainWitness u) : Set (↥(pools (start + u.val)))) := by
      simpa [chainWitness] using (hchains u).choose_spec.2
    let selectedPools : ℕ → Finset (Point 2) := fun i ↦
      if hi : i < m then
        (chainWitness ⟨i, hi⟩).image (fun p ↦ p.1)
      else
        ∅
    have selectedPools_eq (i : ℕ) (hi : i < m) :
        selectedPools i =
          (chainWitness ⟨i, hi⟩).image (fun p ↦ p.1) := by
      simp [selectedPools, hi]
    have selectedPoolsSubset (i : ℕ) (hi : i < m) :
        selectedPools i ⊆ pools (start + i) := by
      intro p hp
      rw [selectedPools_eq i hi] at hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      exact q.property
    have selectedPoolsCard (i : ℕ) (hi : i < m) :
        chainSize ≤ (selectedPools i).card := by
      rw [selectedPools_eq i hi,
        Finset.card_image_of_injective _ Subtype.val_injective]
      exact chainWitnessCard ⟨i, hi⟩
    have selectedPoolsChain (i : ℕ) (hi : i < m) :
        ∀ ⦃p⦄, p ∈ selectedPools i →
          ∀ ⦃q⦄, q ∈ selectedPools i → p ≠ q →
            SukRegionLE
                (anchors (start + i)) (anchors (start + i + 3)) p q ∨
              SukRegionLE
                (anchors (start + i)) (anchors (start + i + 3)) q p := by
      intro p hp q hq hpq
      rw [selectedPools_eq i hi] at hp hq
      rcases Finset.mem_image.mp hp with ⟨p', hp', rfl⟩
      rcases Finset.mem_image.mp hq with ⟨q', hq', rfl⟩
      have hpq' : p' ≠ q' := by
        intro hpq'
        apply hpq
        exact congrArg Subtype.val hpq'
      exact chainWitnessIsChain ⟨i, hi⟩ hp' hq' hpq'
    let intervalAnchors : ℕ → Point 2 := fun i ↦ anchors (start + i)
    have intervalStrictCap :
        SukStrictCapSequence (m + 3) intervalAnchors := by
      intro i j k hij hjk hk
      simpa [intervalAnchors] using hraw.strictCap
        (Nat.add_lt_add_left hij start)
        (Nat.add_lt_add_left hjk start) (by omega)
    have anchorMemRaw (i : ℕ) (hi : i < m + 3) :
        intervalAnchors i ∈
          (Finset.range (L + 3)).image anchors ∪
            (Finset.range L).biUnion pools := by
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨start + i, Finset.mem_range.mpr (by omega), rfl⟩
    have selectedPoolMemRaw (i : ℕ) (hi : i < m)
        {p : Point 2} (hp : p ∈ selectedPools i) :
        p ∈ (Finset.range (L + 3)).image anchors ∪
          (Finset.range L).biUnion pools := by
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨start + i, Finset.mem_range.mpr (by omega),
        selectedPoolsSubset i hi hp⟩
    have selectedAdjacent :
        SukConsecutiveChainPools m intervalAnchors selectedPools := by
      intro i hi
      have hiM : i < m := by omega
      refine {
        anchorsCap := ⟨
          intervalStrictCap (by omega) (by omega) (by omega),
          intervalStrictCap (by omega) (by omega) (by omega),
          intervalStrictCap (by omega) (by omega) (by omega),
          intervalStrictCap (by omega) (by omega) (by omega),
          intervalStrictCap (by omega) (by omega) (by omega),
          intervalStrictCap (by omega) (by omega) (by omega),
          intervalStrictCap (by omega) (by omega) (by omega),
          intervalStrictCap (by omega) (by omega) (by omega),
          intervalStrictCap (by omega) (by omega) (by omega),
          intervalStrictCap (by omega) (by omega) (by omega)⟩
        disjoint := ?_
        generalPosition := ?_
        leftRegion := ?_
        rightRegion := ?_
        leftChain := ?_
        rightChain := ?_
      }
      · exact Disjoint.mono
          (selectedPoolsSubset i hiM)
          (selectedPoolsSubset (i + 1) hi)
          (hraw.disjoint (start + i) (by omega))
      · apply hraw.generalPosition.mono
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_union] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | hp
        · exact anchorMemRaw i (by omega)
        · exact anchorMemRaw (i + 1) (by omega)
        · exact anchorMemRaw (i + 2) (by omega)
        · exact anchorMemRaw (i + 3) (by omega)
        · exact anchorMemRaw (i + 4) (by omega)
        · exact hp.elim
            (selectedPoolMemRaw i hiM)
            (selectedPoolMemRaw (i + 1) hi)
      · intro p hp
        simpa [intervalAnchors, Nat.add_assoc] using
          hraw.region (start + i) (by omega)
            (selectedPoolsSubset i hiM hp)
      · intro p hp
        simpa [intervalAnchors, Nat.add_assoc] using
          hraw.region (start + (i + 1)) (by omega)
            (selectedPoolsSubset (i + 1) hi hp)
      · intro p hp q hq hpq
        simpa [intervalAnchors, Nat.add_assoc] using
          selectedPoolsChain i hiM hp hq hpq
      · intro p hp q hq hpq
        simpa [intervalAnchors, Nat.add_assoc] using
          selectedPoolsChain (i + 1) hi hp hq hpq
    have selectedContains :
        ContainsConvexSubset
          (SukConsecutivePoolCarrier m selectedPools) n := by
      apply sukConsecutiveChainPools_containsConvexSubset
        m n K intervalAnchors selectedPools hm hK selectedAdjacent
        hfinalDeficit hfinalSize
      intro i hi
      exact (hchainCard i hi).trans_le (selectedPoolsCard i hi)
    have selectedCarrierSubset :
        SukConsecutivePoolCarrier m selectedPools ⊆
          SukConsecutivePoolCarrier L pools := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hp⟩
      have hiM : i < m := Finset.mem_range.mp hi
      apply Finset.mem_biUnion.mpr
      exact ⟨start + i, Finset.mem_range.mpr (by omega),
        selectedPoolsSubset i hiM hp⟩
    rcases selectedContains with
      ⟨selected, hselectedSubset, hselectedCard, hselectedConvex⟩
    exact Or.inl ⟨selected, hselectedSubset.trans selectedCarrierSubset,
      hselectedCard, hselectedConvex⟩

end

end ErdosSzekeres

end
