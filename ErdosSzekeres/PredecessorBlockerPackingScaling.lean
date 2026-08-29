module

public import ErdosSzekeres.PredecessorHalfFin15Obstruction

@[expose] public section

/-!
# Scaling the blocker-complement packing argument

This file isolates the incidence bound behind the seven-point blocker collision
at fifteen points.  It also records a kernel-checked packing at the next
parameter, showing that this incidence argument alone does not force the same
collision on a nine-point support.
-/

namespace ErdosSzekeres

/-- Pairwise-small intersections of `r`-blocks on a `(2r-1)`-point support
give a packing of their `(r-1)`-point complements by `(r-2)`-subsets. -/
theorem blocker_complement_packing_bound {α : Type*} [DecidableEq α] (r : ℕ)
    (support : Finset α) (family : Finset (Finset α)) (hr : 2 ≤ r)
    (hsupport : support.card = 2 * r - 1)
    (hsub : ∀ block ∈ family, block ⊆ support)
    (hcard : ∀ block ∈ family, block.card = r)
    (hinter : ∀ a ∈ family, ∀ b ∈ family, a ≠ b → (a ∩ b).card ≤ r - 2) :
    family.card * (r - 1) ≤ Nat.choose (2 * r - 1) (r - 2) := by
  classical
  let smalls := support.powersetCard (r - 2)
  let complement : Finset α → Finset α := fun block ↦ support \ block
  have hcomplementSub : ∀ block ∈ family, complement block ⊆ support := by
    intro block _hblock
    exact Finset.sdiff_subset
  have hcomplementCard : ∀ block ∈ family, (complement block).card = r - 1 := by
    intro block hblock
    simp only [complement]
    rw [Finset.card_sdiff_of_subset (hsub block hblock), hsupport, hcard block hblock]
    omega
  have hdegreeLe : ∀ small ∈ smalls,
      (family.filter fun block ↦ small ⊆ complement block).card ≤ 1 := by
    intro small hsmall
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have haData := Finset.mem_filter.mp ha
    have hbData := Finset.mem_filter.mp hb
    by_contra hab
    have hinterAB := hinter a haData.1 b hbData.1 hab
    have hsmallData : small ⊆ support ∧ small.card = r - 2 := by
      simpa [smalls] using Finset.mem_powersetCard.mp hsmall
    have hunionSub : a ∪ b ⊆ support :=
      Finset.union_subset (hsub a haData.1) (hsub b hbData.1)
    have hdisjoint : Disjoint small (a ∪ b) := by
      apply Finset.disjoint_left.mpr
      intro x hxSmall hxUnion
      rcases Finset.mem_union.mp hxUnion with hxa | hxb
      · exact (Finset.mem_sdiff.mp (haData.2 hxSmall)).2 hxa
      · exact (Finset.mem_sdiff.mp (hbData.2 hxSmall)).2 hxb
    have hcombinedSub : small ∪ (a ∪ b) ⊆ support :=
      Finset.union_subset hsmallData.1 hunionSub
    have hunionCardLower : r + 2 ≤ (a ∪ b).card := by
      have hunionInter := Finset.card_union_add_card_inter a b
      rw [hcard a haData.1, hcard b hbData.1] at hunionInter
      omega
    have hcombinedCardLe : small.card + (a ∪ b).card ≤ support.card := by
      rw [← Finset.card_union_of_disjoint hdisjoint]
      exact Finset.card_le_card hcombinedSub
    omega
  have hdoubleCount :
      (∑ small ∈ smalls,
        (family.filter fun block ↦ small ⊆ complement block).card) =
      ∑ block ∈ family,
        (smalls.filter fun small ↦ small ⊆ complement block).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hfilter : ∀ block ∈ family,
      smalls.filter (fun small ↦ small ⊆ complement block) =
        (complement block).powersetCard (r - 2) := by
    intro block hblock
    ext small
    simp only [Finset.mem_filter, smalls, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_hsmallSupport, hsmallCard⟩, hsmallComplement⟩
      exact ⟨hsmallComplement, hsmallCard⟩
    · rintro ⟨hsmallComplement, hsmallCard⟩
      exact ⟨⟨hsmallComplement.trans (hcomplementSub block hblock), hsmallCard⟩,
        hsmallComplement⟩
  have hfilterCard : ∀ block ∈ family,
      (smalls.filter fun small ↦ small ⊆ complement block).card = r - 1 := by
    intro block hblock
    rw [hfilter block hblock, Finset.card_powersetCard, hcomplementCard block hblock]
    have hrPred : r - 1 = (r - 2) + 1 := by omega
    rw [hrPred]
    exact Nat.choose_succ_self_right (r - 2)
  have htotal :
      (∑ small ∈ smalls,
        (family.filter fun block ↦ small ⊆ complement block).card) =
      family.card * (r - 1) := by
    rw [hdoubleCount]
    calc
      (∑ block ∈ family,
          (smalls.filter fun small ↦ small ⊆ complement block).card) =
          ∑ _block ∈ family, (r - 1) := by
            apply Finset.sum_congr rfl
            exact hfilterCard
      _ = family.card * (r - 1) := by simp
  have hupper :
      (∑ small ∈ smalls,
        (family.filter fun block ↦ small ⊆ complement block).card) ≤
      smalls.card := by
    calc
      (∑ small ∈ smalls,
          (family.filter fun block ↦ small ⊆ complement block).card) ≤
          ∑ _small ∈ smalls, 1 := by
            apply Finset.sum_le_sum
            exact hdegreeLe
      _ = smalls.card := by simp
  calc
    family.card * (r - 1) =
        ∑ small ∈ smalls,
          (family.filter fun block ↦ small ⊆ complement block).card := htotal.symm
    _ ≤ smalls.card := hupper
    _ = Nat.choose support.card (r - 2) := Finset.card_powersetCard _ _
    _ = Nat.choose (2 * r - 1) (r - 2) := by rw [hsupport]

/-- At the Fin15 parameter, at most seven four-blockers can have all pairwise
intersections of size at most two. -/
theorem four_blocker_family_card_le_seven {α : Type*} [DecidableEq α]
    (support : Finset α) (family : Finset (Finset α))
    (hsupport : support.card = 7)
    (hsub : ∀ block ∈ family, block ⊆ support)
    (hcard : ∀ block ∈ family, block.card = 4)
    (hinter : ∀ a ∈ family, ∀ b ∈ family, a ≠ b → (a ∩ b).card ≤ 2) :
    family.card ≤ 7 := by
  have hbound := blocker_complement_packing_bound 4 support family (by omega)
    (by omega) hsub hcard (by simpa using hinter)
  norm_num [Nat.choose] at hbound ⊢
  omega

private def blockerPackingR5Family : Finset (Finset (Fin 9)) :=
  { {4, 5, 6, 7, 8},
    {2, 3, 6, 7, 8},
    {2, 3, 4, 5, 8},
    {1, 3, 5, 7, 8},
    {1, 3, 4, 6, 8},
    {1, 2, 5, 6, 8},
    {1, 2, 4, 7, 8},
    {0, 3, 5, 6, 8},
    {0, 3, 4, 7, 8},
    {0, 2, 5, 7, 8} }

/-- Ten five-blockers on nine points can have every distinct pair intersect in
at most three points.  Thus the Fin15 packing collision does not extend to the
next parameter from incidence counting alone. -/
theorem exists_ten_five_blockers_fin9 :
    ∃ family : Finset (Finset (Fin 9)),
      family.card = 10 ∧
        (∀ block ∈ family, block ⊆ Finset.univ) ∧
        (∀ block ∈ family, block.card = 5) ∧
        ∀ a ∈ family, ∀ b ∈ family, a ≠ b → (a ∩ b).card ≤ 3 := by
  refine ⟨blockerPackingR5Family, ?_, ?_, ?_, ?_⟩
  · decide
  · intro block _hblock
    exact Finset.subset_univ block
  · set_option maxRecDepth 100000 in
      decide
  · set_option maxRecDepth 100000 in
      decide

end ErdosSzekeres

end
