module

public import ErdosSzekeres.HMPTCyclicNoTarget
public import ErdosSzekeres.HMPTHorizontalChainConvexity
public import ErdosSzekeres.HMPTParityInnerGluing

@[expose] public section

/-!
# Cyclic HMPT horizontal profiles without a target convex polygon

This file packages the exact H2 profile family and one dependently attached H3
profile per source pool.  It retains the adjacent H2 inequalities and derives
the outer-chain and parity inner-chain bounds needed by the finite HMPT
aggregation layer.
-/

namespace ErdosSzekeres

noncomputable section

open scoped BigOperators

/-- The exact cyclic H2/H3 family together with all no-target inequalities
produced by the fourth finite HMPT layer. -/
structure HMPTCyclicHorizontalProfilePackage
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r) (n : ℕ) where
  verticalProfile : ∀ i : Fin (2 * r),
    HMPTVerticalProfile
      (h.hmptAnchor i 0) (h.hmptAnchor i 1)
      (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i)
  horizontalProfile : ∀ i : Fin (2 * r),
    HMPTHorizontalProfile
      (h.hmptAnchor i 0) (h.hmptAnchor i 1)
      (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i)
      (verticalProfile i)
  adjacentCard_lt : ∀ i : Fin (2 * r),
    (verticalProfile i).rightChain.card +
      (verticalProfile (hmptCyclicSucc i)).leftChain.card < n
  outerCard_lt : ∀ i : Fin (2 * r),
    (horizontalProfile i).outerChain.card < n
  parityInnerCard_lt : ∀ parity : Fin 2,
    (∑ i ∈ Finset.univ.filter
      (fun i : Fin (2 * r) ↦ i.val % 2 = parity.val),
        (horizontalProfile i).innerChain.card) < n
  totalInnerCard_lt :
    (∑ i : Fin (2 * r), (horizontalProfile i).innerChain.card) < 2 * n

private theorem convex_card_lt_of_subset_noTarget_f4
    {P s : Finset (Point 2)} {n : ℕ}
    (hsubset : s ⊆ P)
    (hconvex : InConvexPosition s)
    (hno : ¬ContainsConvexSubset P n) :
    s.card < n := by
  by_contra hnot
  have hn : n ≤ s.card := by omega
  obtain ⟨selected, hselected, hselectedCard⟩ :=
    Finset.exists_subset_card_eq hn
  apply hno
  exact ⟨selected, hselected.trans hsubset, hselectedCard,
    hconvex.mono hselected⟩

private theorem innerPoints_pairwiseDisjoint_f4
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r)
    (geometry : HMPTCyclicSpikeGeometry P r h)
    (verticalProfile : ∀ i : Fin (2 * r),
      HMPTVerticalProfile
        (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i))
    (horizontalProfile : ∀ i : Fin (2 * r),
      HMPTHorizontalProfile
        (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i)
        (verticalProfile i))
    (selected : Finset (Fin (2 * r))) :
    (selected : Set (Fin (2 * r))).PairwiseDisjoint
      (fun i ↦ hmptChainPoints (horizontalProfile i).innerChain) := by
  intro i _ j _ hij
  exact (geometry.pools_disjoint i j hij).mono
    (hmptChainPoints_subset (horizontalProfile i).innerChain)
    (hmptChainPoints_subset (horizontalProfile j).innerChain)

private theorem innerPoints_biUnion_subset_f4
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r)
    (geometry : HMPTCyclicSpikeGeometry P r h)
    (verticalProfile : ∀ i : Fin (2 * r),
      HMPTVerticalProfile
        (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i))
    (horizontalProfile : ∀ i : Fin (2 * r),
      HMPTHorizontalProfile
        (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i)
        (verticalProfile i))
    (selected : Finset (Fin (2 * r))) :
    selected.biUnion
      (fun i ↦ hmptChainPoints (horizontalProfile i).innerChain) ⊆ P := by
  intro p hp
  obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp
  exact geometry.pool_subset i
    (hmptChainPoints_subset (horizontalProfile i).innerChain hpi)

namespace PorValtrSupportProductData

/-- Under the absence of a convex `n`-subset, choose the H2 family once and
attach one H3 profile to each exact member, retaining all H2--H4 inequalities
needed by the later product aggregation. -/
theorem exists_hmptCyclicHorizontalProfilePackage
    {P : Finset (Point 2)} {r n : ℕ}
    (h : PorValtrSupportProductData P r)
    (hr : 3 ≤ r)
    (hgp : InGeneralPosition P)
    (hno : ¬ContainsConvexSubset P n) :
    Nonempty (HMPTCyclicHorizontalProfilePackage h n) := by
  classical
  obtain ⟨verticalProfile, hadjacent⟩ :=
    h.exists_hmptCyclicProfiles hr hgp hno
  let geometry : HMPTCyclicSpikeGeometry P r h :=
    h.toHMPTCyclicSpikeGeometry hr hgp
  let horizontalProfile : ∀ i : Fin (2 * r),
      HMPTHorizontalProfile
        (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i)
        (verticalProfile i) :=
    fun i ↦ Classical.choice
      ((geometry.localRegion i).exists_hmptHorizontalProfile
        (verticalProfile i))
  have houter : ∀ i : Fin (2 * r),
      (horizontalProfile i).outerChain.card < n := by
    intro i
    simpa only [hmptChainPoints_card] using
      convex_card_lt_of_subset_noTarget_f4
        (P := P)
        (s := hmptChainPoints (horizontalProfile i).outerChain)
        (n := n)
        ((hmptChainPoints_subset
          (horizontalProfile i).outerChain).trans
            (geometry.pool_subset i))
        ((geometry.localRegion i).hmptOuterHorizontalChain_convex
          (verticalProfile i) (horizontalProfile i)) hno
  have hparity : ∀ parity : Fin 2,
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin (2 * r) ↦ i.val % 2 = parity.val),
          (horizontalProfile i).innerChain.card) < n := by
    intro parity
    let selected := Finset.univ.filter
      (fun i : Fin (2 * r) ↦ i.val % 2 = parity.val)
    let family : Fin (2 * r) → Finset (Point 2) := fun i ↦
      hmptChainPoints (horizontalProfile i).innerChain
    let union := selected.biUnion family
    have hpairwise : (selected : Set (Fin (2 * r))).PairwiseDisjoint family :=
      innerPoints_pairwiseDisjoint_f4 h geometry verticalProfile
        horizontalProfile selected
    have hcard : union.card =
        ∑ i ∈ selected, (horizontalProfile i).innerChain.card := by
      dsimp only [union]
      rw [Finset.card_biUnion hpairwise]
      apply Finset.sum_congr rfl
      intro i _
      exact hmptChainPoints_card (horizontalProfile i).innerChain
    have hsubset : union ⊆ P := by
      exact innerPoints_biUnion_subset_f4 h geometry verticalProfile
        horizontalProfile selected
    have hconvex : InConvexPosition union := by
      dsimp only [union, family, selected]
      exact h.hmptParityInnerUnion_convex hr hgp verticalProfile
        horizontalProfile parity
    have hunionCard : union.card < n :=
      convex_card_lt_of_subset_noTarget_f4 hsubset hconvex hno
    dsimp only [selected] at hcard
    rw [← hcard]
    exact hunionCard
  have htotal :
      (∑ i : Fin (2 * r), (horizontalProfile i).innerChain.card) <
        2 * n := by
    let zero : Fin 2 := ⟨0, by decide⟩
    let one : Fin 2 := ⟨1, by decide⟩
    have hzero := hparity zero
    have hone := hparity one
    have hnotZeroEqOne : ∀ i : Fin (2 * r),
        (¬i.val % 2 = zero.val) ↔ i.val % 2 = one.val := by
      intro i
      have hmod : i.val % 2 < 2 := Nat.mod_lt _ (by decide)
      simp only [zero, one]
      omega
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin (2 * r)))
      (fun i ↦ i.val % 2 = zero.val)
      (fun i ↦ (horizontalProfile i).innerChain.card)]
    have hsecond :
        (∑ i ∈ Finset.univ.filter
          (fun i : Fin (2 * r) ↦ ¬i.val % 2 = zero.val),
            (horizontalProfile i).innerChain.card) =
          ∑ i ∈ Finset.univ.filter
            (fun i : Fin (2 * r) ↦ i.val % 2 = one.val),
              (horizontalProfile i).innerChain.card := by
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hnotZeroEqOne i
      · intro i _
        rfl
    rw [hsecond]
    omega
  exact ⟨{
    verticalProfile := verticalProfile
    horizontalProfile := horizontalProfile
    adjacentCard_lt := hadjacent
    outerCard_lt := houter
    parityInnerCard_lt := hparity
    totalInnerCard_lt := htotal
  }⟩

end PorValtrSupportProductData

end

end ErdosSzekeres
