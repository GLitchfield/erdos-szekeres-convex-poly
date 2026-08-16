module

public import ErdosSzekeres.SukCyclicSupportContraction
public import ErdosSzekeres.SukMarkedEdgeBlocks

@[expose] public section

/-!
# Pór--Valtr cyclic support bridge

This module transports marked source pools through a strict cyclic cap contraction.
It produces only raw consecutive support pools, preserving their source cardinalities.
-/

namespace ErdosSzekeres

noncomputable section

/-- Source-authentic cyclic support data with marked rich pools. -/
structure PorValtrCyclicSupportData (r q : ℕ) where
  anchors : ℕ → Point 2
  carrier : Finset (Point 2)
  marked : Finset ℕ
  sourcePool : ℕ → Finset (Point 2)
  strictCap : SukStrictCapSequence (2 * r) anchors
  markedSubset : marked ⊆ Finset.range (2 * r)
  markedCard : marked.card = r
  anchorsSubset : ∀ ⦃i : ℕ⦄, i < 2 * r → anchors i ∈ carrier
  sourcePoolSubset : ∀ ⦃i : ℕ⦄, i ∈ marked → sourcePool i ⊆ carrier
  sourcePoolsDisjoint : ∀ ⦃i : ℕ⦄, i ∈ marked →
    ∀ ⦃j : ℕ⦄, j ∈ marked → i ≠ j →
      Disjoint (sourcePool i) (sourcePool j)
  generalPosition : InGeneralPosition carrier
  sourceCard : ∀ ⦃i : ℕ⦄, i ∈ marked → q ≤ (sourcePool i).card
  sourceRegion : ∀ ⦃i : ℕ⦄, i ∈ marked → 0 < i →
    ∀ ⦃p : Point 2⦄, p ∈ sourcePool i →
      p ∈ SukSupportRegion
        (anchors (i - 1)) (anchors i)
        (anchors (i + 1)) (anchors (i + 2))

/-- Consecutive raw target pools with their exact support geometry. -/
structure SukConsecutiveRawPools
    (L : ℕ) (anchors : ℕ → Point 2)
    (pools : ℕ → Finset (Point 2)) : Prop where
  strictCap : SukStrictCapSequence (L + 3) anchors
  disjoint : ∀ i, i + 1 < L → Disjoint (pools i) (pools (i + 1))
  generalPosition : InGeneralPosition
    ((Finset.range (L + 3)).image anchors ∪
      (Finset.range L).biUnion pools)
  region : ∀ i, i < L → ∀ ⦃p : Point 2⦄, p ∈ pools i →
    p ∈ SukSupportRegion
      (anchors i) (anchors (i + 1))
      (anchors (i + 2)) (anchors (i + 3))

/-- Marked cyclic source cells produce the internal raw consecutive Suk pools. -/
theorem PorValtrCyclicSupportData.toSukConsecutiveRawPools
    {r q : ℕ} (h : PorValtrCyclicSupportData r q) (hr : 5 ≤ r) :
    ∃ targetAnchors : ℕ → Point 2,
    ∃ targetPools : ℕ → Finset (Point 2),
      SukConsecutiveRawPools (r - 3) targetAnchors targetPools ∧
      ∀ i, i < r - 3 → q ≤ (targetPools i).card := by
  classical
  rcases exists_sukMarkedEdgeBlockSelection r h.marked (by omega)
      h.markedSubset h.markedCard with
    ⟨selected, hselectedMono, hselectedBound, hblocks⟩
  let blockEdge : Fin (r - 1) → ℕ := fun j ↦ (hblocks j).choose
  have hblockEdgeMem (j : Fin (r - 1)) : blockEdge j ∈ h.marked := by
    exact (hblocks j).choose_spec.1
  have hblockEdgeLower (j : Fin (r - 1)) :
      selected ⟨j, by omega⟩ ≤ blockEdge j := by
    exact (hblocks j).choose_spec.2.1
  have hblockEdgeUpper (j : Fin (r - 1)) :
      blockEdge j < selected ⟨j + 1, by omega⟩ := by
    exact (hblocks j).choose_spec.2.2
  let rawEdge (i : ℕ) (hi : i < r - 3) : ℕ :=
    blockEdge ⟨i + 1, by omega⟩
  have hrawEdgeMem (i : ℕ) (hi : i < r - 3) : rawEdge i hi ∈ h.marked := by
    exact hblockEdgeMem ⟨i + 1, by omega⟩
  have hrawEdgeLower (i : ℕ) (hi : i < r - 3) :
      selected ⟨i + 1, by omega⟩ ≤ rawEdge i hi := by
    exact hblockEdgeLower ⟨i + 1, by omega⟩
  have hrawEdgeUpper (i : ℕ) (hi : i < r - 3) :
      rawEdge i hi < selected ⟨i + 2, by omega⟩ := by
    exact hblockEdgeUpper ⟨i + 1, by omega⟩
  let targetAnchors : ℕ → Point 2 := fun i ↦
    if hi : i < r then h.anchors (selected ⟨i, hi⟩) else h.anchors 0
  let targetPools : ℕ → Finset (Point 2) := fun i ↦
    if hi : i < r - 3 then h.sourcePool (rawEdge i hi) else ∅
  have htargetAnchors (i : ℕ) (hi : i < r) :
      targetAnchors i = h.anchors (selected ⟨i, hi⟩) := by
    simp [targetAnchors, hi]
  have htargetPools (i : ℕ) (hi : i < r - 3) :
      targetPools i = h.sourcePool (rawEdge i hi) := by
    simp [targetPools, hi]
  refine ⟨targetAnchors, targetPools, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j k hij hjk hk
      have hiR : i < r := by omega
      have hjR : j < r := by omega
      have hkR : k < r := by omega
      rw [htargetAnchors i hiR, htargetAnchors j hjR, htargetAnchors k hkR]
      apply h.strictCap
      · apply hselectedMono
        exact hij
      · apply hselectedMono
        exact hjk
      · exact hselectedBound ⟨k, hkR⟩
    · intro i hi
      have hiLeft : i < r - 3 := by omega
      have hiRight : i + 1 < r - 3 := by omega
      rw [htargetPools i hiLeft, htargetPools (i + 1) hiRight]
      apply h.sourcePoolsDisjoint (hrawEdgeMem i hiLeft)
        (hrawEdgeMem (i + 1) hiRight)
      have hupper := hrawEdgeUpper i hiLeft
      have hlower := hrawEdgeLower (i + 1) hiRight
      have hmiddle :
          (⟨i + 2, by omega⟩ : Fin r) = ⟨i + 1 + 1, by omega⟩ := by
        rfl
      rw [← hmiddle] at hlower
      exact Nat.ne_of_lt (hupper.trans_le hlower)
    · apply h.generalPosition.mono
      intro p hp
      rcases Finset.mem_union.mp hp with hpAnchor | hpPool
      · rcases Finset.mem_image.mp hpAnchor with ⟨i, hi, rfl⟩
        have hiR : i < r := by
          have := Finset.mem_range.mp hi
          omega
        rw [htargetAnchors i hiR]
        exact h.anchorsSubset (hselectedBound ⟨i, hiR⟩)
      · rcases Finset.mem_biUnion.mp hpPool with ⟨i, hi, hp⟩
        have hiL : i < r - 3 := Finset.mem_range.mp hi
        rw [htargetPools i hiL] at hp
        exact h.sourcePoolSubset (hrawEdgeMem i hiL) hp
    · intro i hi p hp
      have hi0 : i < r := by omega
      have hi1 : i + 1 < r := by omega
      have hi2 : i + 2 < r := by omega
      have hi3 : i + 3 < r := by omega
      rw [htargetPools i hi] at hp
      rw [htargetAnchors i hi0, htargetAnchors (i + 1) hi1,
        htargetAnchors (i + 2) hi2, htargetAnchors (i + 3) hi3]
      let edge := rawEdge i hi
      have hedgeMem : edge ∈ h.marked := hrawEdgeMem i hi
      have hedgeLower : selected ⟨i + 1, hi1⟩ ≤ edge := by
        simpa [edge] using hrawEdgeLower i hi
      have hedgeUpper : edge < selected ⟨i + 2, hi2⟩ := by
        simpa [edge] using hrawEdgeUpper i hi
      have hselectedBefore :
          selected ⟨0, by omega⟩ < selected ⟨i + 1, hi1⟩ := by
        apply hselectedMono
        change 0 < i + 1
        omega
      have hedgePos : 0 < edge := by omega
      have hsource := h.sourceRegion hedgeMem hedgePos hp
      have hedgeOne : edge - 1 + 1 = edge := by omega
      have hedgeTwo : edge - 1 + 2 = edge + 1 := by omega
      have hedgeThree : edge - 1 + 3 = edge + 2 := by omega
      apply sukSupportRegion_subset_of_strictCapBlock
        (2 * r)
        (selected ⟨i, hi0⟩)
        (selected ⟨i + 1, hi1⟩)
        (selected ⟨i + 2, hi2⟩)
        (selected ⟨i + 3, hi3⟩)
        (edge - 1) h.anchors h.strictCap
      · apply hselectedMono
        change i < i + 1
        omega
      · omega
      · omega
      · apply hselectedMono
        change i + 2 < i + 3
        omega
      · exact hselectedBound ⟨i + 3, hi3⟩
      · simpa only [hedgeOne, hedgeTwo, hedgeThree] using hsource
  · intro i hi
    rw [htargetPools i hi]
    exact h.sourceCard (hrawEdgeMem i hi)

end

end ErdosSzekeres

end
