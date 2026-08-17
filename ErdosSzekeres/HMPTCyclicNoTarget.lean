module

public import ErdosSzekeres.HMPTAdjacentSpikeGluing
public import ErdosSzekeres.HMPTCyclicSpikeProducer
public import ErdosSzekeres.HMPTVerticalProfileProducer

@[expose] public section

/-!
# Cyclic HMPT profiles without a target convex polygon

This file composes the cyclic spike geometry, the local vertical-profile
producer, and adjacent selected-chain gluing.  If the original carrier has no
convex `n`-subset, every adjacent selected-chain pair has total size below
`n`.
-/

namespace ErdosSzekeres

noncomputable section

private theorem hmptCyclic_anchor_succ_c4
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (_hr : 3 ≤ r)
    (i : Fin (2 * r)) (offset : ℕ) (hoffset : offset + 1 < 5) :
    h.hmptAnchor (hmptCyclicSucc i) ⟨offset, by omega⟩ =
      h.hmptAnchor i ⟨offset + 1, hoffset⟩ := by
  unfold PorValtrSupportProductData.hmptAnchor hmptCyclicSucc
  apply congrArg h.anchors
  calc
    ((i.1 + 1) % (2 * r) + (2 * r - 1) + offset) % (2 * r) =
        (i.1 + 1 + (2 * r - 1 + offset)) % (2 * r) := by
      rw [Nat.add_assoc, Nat.mod_add_mod]
    _ = (i.1 + (2 * r - 1) + (offset + 1)) % (2 * r) := by
      congr 1
      omega

private theorem right_left_union_convex_of_anchor_eq_c4
    {x0 x1 x2 x3 x4 y0 y1 y2 y3 : Point 2}
    {leftPool rightPool : Finset (Point 2)}
    (hy0 : y0 = x1) (hy1 : y1 = x2)
    (hy2 : y2 = x3) (hy3 : y3 = x4)
    (geometry : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (leftProfile : HMPTVerticalProfile x0 x1 x2 x3 leftPool)
    (rightProfile : HMPTVerticalProfile y0 y1 y2 y3 rightPool) :
    InConvexPosition
      (hmptChainPoints leftProfile.rightChain ∪
        hmptChainPoints rightProfile.leftChain) := by
  subst y0
  subst y1
  subst y2
  subst y3
  exact geometry.right_left_union_convex leftProfile rightProfile

private theorem hmptCyclic_right_left_union_convex_c4
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (hr : 3 ≤ r)
    (geometry : HMPTCyclicSpikeGeometry P r h)
    (profile : ∀ i : Fin (2 * r),
      HMPTVerticalProfile
        (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i))
    (i : Fin (2 * r)) :
    InConvexPosition
      (hmptChainPoints (profile i).rightChain ∪
        hmptChainPoints (profile (hmptCyclicSucc i)).leftChain) := by
  apply right_left_union_convex_of_anchor_eq_c4
    (hmptCyclic_anchor_succ_c4 h hr i 0 (by decide))
    (hmptCyclic_anchor_succ_c4 h hr i 1 (by decide))
    (hmptCyclic_anchor_succ_c4 h hr i 2 (by decide))
    (hmptCyclic_anchor_succ_c4 h hr i 3 (by decide))
    (geometry.adjacentGeometry i) (profile i)
    (profile (hmptCyclicSucc i))

namespace PorValtrSupportProductData

/-- Under the absence of a convex `n`-subset in the original carrier, choose
all cyclic HMPT profiles so that every adjacent right/left selected-chain pair
has total cardinality below `n`. -/
theorem exists_hmptCyclicProfiles
    {P : Finset (Point 2)} {r n : ℕ}
    (h : PorValtrSupportProductData P r)
    (hr : 3 ≤ r)
    (hgp : InGeneralPosition P)
    (hno : ¬ ContainsConvexSubset P n) :
    ∃ profile : ∀ i : Fin (2 * r),
        HMPTVerticalProfile
          (h.hmptAnchor i 0) (h.hmptAnchor i 1)
          (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i),
      ∀ i : Fin (2 * r),
        (profile i).rightChain.card +
          (profile (hmptCyclicSucc i)).leftChain.card < n := by
  classical
  let geometry : HMPTCyclicSpikeGeometry P r h :=
    h.toHMPTCyclicSpikeGeometry hr hgp
  let profile : ∀ i : Fin (2 * r),
      HMPTVerticalProfile
        (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i) :=
    fun i ↦ Classical.choice
      (geometry.localRegion i).exists_hmptVerticalProfile
  refine ⟨profile, ?_⟩
  intro i
  by_contra hnot
  have hsum : n ≤
      (profile i).rightChain.card +
        (profile (hmptCyclicSucc i)).leftChain.card := by
    omega
  let rightPoints := hmptChainPoints (profile i).rightChain
  let leftPoints :=
    hmptChainPoints (profile (hmptCyclicSucc i)).leftChain
  let glued := rightPoints ∪ leftPoints
  have hdisjoint : Disjoint rightPoints leftPoints := by
    apply (geometry.adjacentGeometry i).disjoint.mono
    · exact hmptChainPoints_subset (profile i).rightChain
    · exact hmptChainPoints_subset
        (profile (hmptCyclicSucc i)).leftChain
  have hgluedCard : glued.card =
      (profile i).rightChain.card +
        (profile (hmptCyclicSucc i)).leftChain.card := by
    dsimp only [glued, rightPoints, leftPoints]
    rw [Finset.card_union_of_disjoint hdisjoint,
      hmptChainPoints_card, hmptChainPoints_card]
  have hnGlued : n ≤ glued.card := by
    rw [hgluedCard]
    exact hsum
  obtain ⟨selected, hselected, hselectedCard⟩ :=
    Finset.exists_subset_card_eq hnGlued
  have hgluedConvex : InConvexPosition glued := by
    dsimp only [glued, rightPoints, leftPoints]
    exact hmptCyclic_right_left_union_convex_c4 h hr geometry profile i
  have hgluedSubset : glued ⊆ P := by
    intro p hp
    dsimp only [glued, rightPoints, leftPoints] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact geometry.pool_subset i
        (hmptChainPoints_subset (profile i).rightChain hp)
    · exact geometry.pool_subset (hmptCyclicSucc i)
        (hmptChainPoints_subset
          (profile (hmptCyclicSucc i)).leftChain hp)
  apply hno
  exact ⟨selected, hselected.trans hgluedSubset, hselectedCard,
    hgluedConvex.mono hselected⟩

end PorValtrSupportProductData

end

end ErdosSzekeres

end
