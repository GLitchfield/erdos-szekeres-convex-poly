module

public import ErdosSzekeres.SukRegionOrder

@[expose] public section

/-!
# Base separation for an antichain in a Suk support region

This module proves the first geometric step in Suk's antichain-rich case.  The
finite adapter uses `Finset.map` along the value-preserving subtype embedding;
this is extensionally the same subtype finset as the attach/image formulation.
-/

namespace ErdosSzekeres

noncomputable section

/-- The point-level form of incomparability in the common-base triangle order. -/
def SukRegionPairwiseAntichain
    (outerLeft outerRight : Point 2)
    (s : Finset (Point 2)) : Prop :=
  ∀ ⦃p⦄, p ∈ s → ∀ ⦃q⦄, q ∈ s → p ≠ q →
    ¬SukRegionLE outerLeft outerRight p q ∧
      ¬SukRegionLE outerLeft outerRight q p

/-- Two incomparable points above a common base leave both base endpoints on
one strict side of their joining line. -/
theorem SukRegionPairwiseAntichain.base_sameStrictSide
    {outerLeft outerRight : Point 2}
    {s : Finset (Point 2)}
    (hanti : SukRegionPairwiseAntichain outerLeft outerRight s)
    (hside : ∀ p ∈ s, 0 < orientation outerLeft outerRight p)
    (hgp : InGeneralPosition (insert outerLeft (insert outerRight s)))
    {p q : Point 2} (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) :
    SameStrictSide p q outerLeft outerRight := by
  have hpSide := hside p hp
  have hqSide := hside q hq
  have hpOuterLeft : p ≠ outerLeft := by
    intro h
    subst p
    simp at hpSide
  have hqOuterLeft : q ≠ outerLeft := by
    intro h
    subst q
    simp at hqSide
  have hpOuterRight : p ≠ outerRight := by
    intro h
    subst p
    simp at hpSide
  have hqOuterRight : q ≠ outerRight := by
    intro h
    subst q
    simp at hqSide
  have hpMem : p ∈ insert outerLeft (insert outerRight s) := by
    simp [hp]
  have hqMem : q ∈ insert outerLeft (insert outerRight s) := by
    simp [hq]
  have hleftNe : orientation p q outerLeft ≠ 0 :=
    hgp hpMem hqMem (by simp) hpq hpOuterLeft hqOuterLeft
  have hrightNe : orientation p q outerRight ≠ 0 :=
    hgp hpMem hqMem (by simp) hpq hpOuterRight hqOuterRight
  rcases lt_or_gt_of_ne hleftNe with hleftNeg | hleftPos
  · rcases lt_or_gt_of_ne hrightNe with hrightNeg | hrightPos
    · exact Or.inl ⟨hleftNeg, hrightNeg⟩
    · exfalso
      apply (hanti hp hq hpq).1
      apply (mem_convexHull_triangle_iff_of_orientation_pos
        outerLeft outerRight p q hpSide).2
      refine ⟨hqSide.le, ?_, ?_⟩
      · rw [orientation_cyclic' p q outerRight]
        exact hrightPos.le
      · rw [orientation_swap_last p q outerLeft]
        linarith
  · rcases lt_or_gt_of_ne hrightNe with hrightNeg | hrightPos
    · exfalso
      apply (hanti hp hq hpq).2
      apply (mem_convexHull_triangle_iff_of_orientation_pos
        outerLeft outerRight q p hqSide).2
      refine ⟨hpSide.le, ?_, ?_⟩
      · rw [orientation_cyclic' q p outerRight,
          orientation_swap p q outerRight]
        linarith
      · rw [orientation_cyclic p q outerLeft]
        exact hleftPos.le
    · exact Or.inr ⟨hleftPos, hrightPos⟩

/-- An actual finite `IsAntichain` of included subtypes yields the exact
point-level incomparability predicate. -/
theorem sukRegionPairwiseAntichain_of_isAntichain
    {outerLeft outerRight : Point 2}
    {s t : Finset (Point 2)}
    (ht : t ⊆ s)
    (hanti : IsAntichain
      (fun p q : ↥s => SukRegionLE outerLeft outerRight p q)
      (↑(t.attach.map
        (⟨fun p ↦ ⟨p.1, ht p.2⟩,
          fun _ _ h ↦ Subtype.ext (congrArg (fun x : ↥s ↦ x.1) h)⟩ :
            ↥t ↪ ↥s)) :
        Set (↥s))) :
    SukRegionPairwiseAntichain outerLeft outerRight t := by
  let inclusion : ↥t ↪ ↥s :=
    ⟨fun p ↦ ⟨p.1, ht p.2⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun x : ↥s ↦ x.1) h)⟩
  change IsAntichain
    (fun p q : ↥s => SukRegionLE outerLeft outerRight p q)
    (↑(t.attach.map inclusion) : Set (↥s)) at hanti
  intro p hp q hq hpq
  let p' : ↥s := ⟨p, ht hp⟩
  let q' : ↥s := ⟨q, ht hq⟩
  have hpMem : p' ∈ t.attach.map inclusion := by
    apply Finset.mem_map.mpr
    exact ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩
  have hqMem : q' ∈ t.attach.map inclusion := by
    apply Finset.mem_map.mpr
    exact ⟨⟨q, hq⟩, Finset.mem_attach _ _, rfl⟩
  have hpq' : p' ≠ q' := by
    intro h
    apply hpq
    simpa [p', q'] using congrArg Subtype.val h
  constructor
  · intro hpqLE
    apply hanti hpMem hqMem hpq'
    simpa [p', q'] using hpqLE
  · intro hqpLE
    apply hanti hqMem hpMem hpq'.symm
    simpa [p', q'] using hqpLE

end

end ErdosSzekeres

end
