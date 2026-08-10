module

public import ErdosSzekeres.StructuralChargingNextState578DeficitDensity

@[expose] public section

/-!
# Consuming the mixed blocker-avoiding address rectangle at state `(5,7,8)`

Opposite strict extensions from a common address minimum put a four-cup in
the lower child and a four-cap in the upper child of the same deep split.
The deep-split gluing law then produces a strong eight-set.  Consequently the
mixed rectangle in the blocker-avoiding address classification is impossible
under the open state-578 hypotheses.
-/

namespace ErdosSzekeres

/-- In the absence of a strong eight-set, the blocker-avoiding address matrix
cannot contain strict extensions in both directions from its common minimum. -/
theorem BlockerAvoidingCupSixCapCommonMinimum578.no_oppositeExtensions_of_noStrongEight
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    {matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker}
    (minimum : BlockerAvoidingCupSixCapCommonMinimum578 matrix)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    ¬∃ first second j k leftTail rightTail,
      (matrix.cell first j).path =
          (matrix.cell minimum.row minimum.column).path ++ false :: leftTail ∧
        (matrix.cell second k).path =
          (matrix.cell minimum.row minimum.column).path ++ true :: rightTail := by
  rintro ⟨first, second, j, k, leftTail, rightTail, hleft, hright⟩
  let base := matrix.cell minimum.row minimum.column
  have hfirstLower : first.1 ⊆ base.node.lower :=
    Finset.subset_union_left.trans
      (minimum.cell_union_subset_lower_of_extends hleft)
  have hkUpper : joint.saturation.capAt k ⊆ base.node.upper :=
    Finset.subset_union_right.trans
      (minimum.cell_union_subset_upper_of_extends hright)
  have hcupData := mem_capWitnesses.mp first.mem_cupWitnesses
  have hcapData := mem_capWitnesses.mp (joint.saturation.capAt_mem k)
  have hstrongNode :
      ContainsStrongPolygonSet χ (base.node.lower ∪ base.node.upper) 8 :=
    base.node.deep.containsStrongPolygonSet_of_containsCupCap
      ⟨first.1, hfirstLower, hcupData.2.1,
        isCapSet_dual_iff.mp hcupData.2.2⟩
      ⟨joint.saturation.capAt k, hkUpper, hcapData.2.1, hcapData.2.2⟩
      (by omega)
  exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrongNode
    (tree.splitAtPath_support_subset base.lookup))

/-- Eliminate the mixed rectangle from the raw blocker-avoiding address
classification.  The surviving cases localize all saturated caps in one
child or leave one complete cap column at the common minimum. -/
theorem BlockerAvoidingCupSixCapCommonMinimum578.localizedCaps_or_minimumColumn_of_noStrongEight
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    {matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker}
    (minimum : BlockerAvoidingCupSixCapCommonMinimum578 matrix)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.lower ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.lower.card) ∨
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.upper ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.upper.card) ∨
    ∃ j, ∀ cup, (matrix.cell cup j).path =
      (matrix.cell minimum.row minimum.column).path := by
  rcases minimum.localizedCaps_or_minimumColumn_or_mixedRectangle with
      hlower | hupper | hcolumn | hmixed
  · exact Or.inl hlower
  · exact Or.inr (Or.inl hupper)
  · exact Or.inr (Or.inr hcolumn)
  · rcases hmixed with
      ⟨first, second, j, k, leftTail, rightTail, hleft, hright, _, _⟩
    exact (minimum.no_oppositeExtensions_of_noStrongEight hnoStrong
      ⟨first, second, j, k, leftTail, rightTail, hleft, hright⟩).elim

end ErdosSzekeres

end
