module

public import ErdosSzekeres.PorValtrCyclicSupportBridge
public import ErdosSzekeres.SukPoolIntervalDichotomy
public import ErdosSzekeres.SukRegionChainGeometry

@[expose] public section

/-!
# The global Dilworth split for consecutive Suk pools

This module composes the raw geometry of every consecutive support pool with
the finite one-region Dilworth theorem and the path dichotomy. The conclusion
retains actual subtype-Finset chain and antichain witnesses.
-/

namespace ErdosSzekeres

noncomputable section

def SukRegionHasChainSubset
    (outerLeft outerRight : Point 2)
    (s : Finset (Point 2)) (k : ℕ) : Prop :=
  ∃ t : Finset (↥s),
    k ≤ t.card ∧
      IsChain
        (fun p q : ↥s ↦ SukRegionLE outerLeft outerRight p.1 q.1)
        (↑t : Set (↥s))

def SukRegionHasAntichainSubset
    (outerLeft outerRight : Point 2)
    (s : Finset (Point 2)) (k : ℕ) : Prop :=
  ∃ t : Finset (↥s),
    k ≤ t.card ∧
      IsAntichain
        (fun p q : ↥s ↦ SukRegionLE outerLeft outerRight p.1 q.1)
        (↑t : Set (↥s))

set_option linter.unusedVariables false in
theorem SukConsecutiveRawPools.chainRun_or_antichainPacking
    {L chainSize antiSize t m : ℕ}
    {anchors : ℕ → Point 2}
    {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (hchainSize : 1 ≤ chainSize) (hantiSize : 1 ≤ antiSize)
    (ht : 1 ≤ t) (hm : 1 ≤ m)
    (hL : (2 * t - 1) * m ≤ L)
    (hcard : ∀ i, i < L →
      (chainSize - 1) * (antiSize - 1) < (pools i).card) :
    (∃ selected : Finset (Fin L),
      selected.card = t ∧ PairwiseNonadjacent selected ∧
      ∀ i, i ∈ selected →
        SukRegionHasAntichainSubset
          (anchors i.val) (anchors (i.val + 3))
          (pools i.val) antiSize) ∨
    (∃ start : ℕ, ∃ hstart : start + m ≤ L,
      ∀ u : Fin m,
        SukRegionHasChainSubset
          (anchors (start + u.val))
          (anchors (start + u.val + 3))
          (pools (start + u.val)) chainSize) := by
  classical
  have localGeometry (i : ℕ) (hi : i < L) :
      SukRegionGeometry
        (anchors i) (anchors (i + 1)) (anchors (i + 2)) (anchors (i + 3))
        (pools i) := by
    refine {
      anchorsCap := ?_
      generalPosition := ?_
      region := ?_
    }
    · exact ⟨
        hraw.strictCap (by omega) (by omega) (by omega),
        hraw.strictCap (by omega) (by omega) (by omega),
        hraw.strictCap (by omega) (by omega) (by omega),
        hraw.strictCap (by omega) (by omega) (by omega)⟩
    · apply hraw.generalPosition.mono
      intro p hp
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | rfl | rfl | rfl | hp
      · exact Finset.mem_union_left _ <|
          Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
      · exact Finset.mem_union_left _ <|
          Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), rfl⟩
      · exact Finset.mem_union_left _ <|
          Finset.mem_image.mpr ⟨i + 2, Finset.mem_range.mpr (by omega), rfl⟩
      · exact Finset.mem_union_left _ <|
          Finset.mem_image.mpr ⟨i + 3, Finset.mem_range.mpr (by omega), rfl⟩
      · exact Finset.mem_union_right _ <|
          Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hp⟩
    · intro p hp
      exact hraw.region i hi hp

  have localAlternative (i : Fin L) :
      SukRegionHasChainSubset
          (anchors i.val) (anchors (i.val + 3)) (pools i.val) chainSize ∨
        SukRegionHasAntichainSubset
          (anchors i.val) (anchors (i.val + 3)) (pools i.val) antiSize := by
    let geometry := localGeometry i.val i.isLt
    have hside : ∀ p ∈ pools i.val,
        0 < orientation (anchors i.val) (anchors (i.val + 3)) p := by
      intro p hp
      exact geometry.base_orientation_pos ⟨p, hp⟩
    have hgp : InGeneralPosition
        (insert (anchors i.val) (insert (anchors (i.val + 3)) (pools i.val))) := by
      apply geometry.generalPosition.mono
      intro p hp
      simp only [Finset.mem_insert] at hp ⊢
      rcases hp with rfl | rfl | hp
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hp)))
    obtain ⟨selected, hselected⟩ := sukRegion_chain_or_antichain
      (anchors i.val) (anchors (i.val + 3)) (pools i.val)
      hside hgp (chainSize - 1) (antiSize - 1) (hcard i.val i.isLt)
    rcases hselected with ⟨hselectedCard, hchain⟩ | ⟨hselectedCard, hanti⟩
    · exact Or.inl ⟨selected, by omega, hchain⟩
    · exact Or.inr ⟨selected, by omega, hanti⟩

  let anti : Fin L → Prop := fun i ↦
    SukRegionHasAntichainSubset
      (anchors i.val) (anchors (i.val + 3)) (pools i.val) antiSize
  rcases exists_pairwise_nonadjacent_or_consecutive_run
      L t m ht hm hL anti with hpacking | hrun
  · rcases hpacking with ⟨selected, hselectedCard, hselectedAnti, hselectedPair⟩
    refine Or.inl ⟨selected, hselectedCard, hselectedPair, ?_⟩
    intro i hi
    simpa [anti] using hselectedAnti i hi
  · rcases hrun with ⟨start, hstart, hnotAnti⟩
    refine Or.inr ⟨start, hstart, ?_⟩
    intro u
    have hi : start + u.val < L := by omega
    have hnot : ¬SukRegionHasAntichainSubset
        (anchors (start + u.val)) (anchors (start + u.val + 3))
        (pools (start + u.val)) antiSize := by
      simpa [anti] using hnotAnti u
    rcases localAlternative ⟨start + u.val, hi⟩ with hchain | hanti
    · exact hchain
    · exact (hnot hanti).elim

end

end ErdosSzekeres
