module

public import ErdosSzekeres.StructuralChargingNextState578LocalizedColumn

@[expose] public section

/-!
# A six-column plateau inside the state-578 private-star branch

Strong-eight avoidance makes every strict extension of the full residual
matrix point in one direction.  The four singleton-owned deletion rows then
cannot all extend strictly: that would put the complete source cap and one of
its private cups in the same child while their source-column cell remains at
the lowest separating node.  Consequently one complete row is a plateau.
Its four vertices miss at least two foreign members of the six-cap packing.
-/

namespace ErdosSzekeres

/-- The sharpened residue of a universal-column private star: one private
deletion cup stays at the common-minimum address in all six cap columns and
misses two distinct foreign cap blocks. -/
def MinimumColumnPlateauTwoForeignCaps578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (star : MinimumColumnPrivateResidualStar578 ledger minimum) : Prop :=
  ∃ owner : {x : Fin n // x ∈ joint.saturation.capAt star.column},
    ∃ foreignOne foreignTwo : Fin 6,
      foreignOne ≠ foreignTwo ∧
      foreignOne ≠ star.column ∧
      foreignTwo ≠ star.column ∧
      (∀ j, (matrix.cell (ledger.cupAt star.column owner) j).path =
        (matrix.cell minimum.row minimum.column).path) ∧
      (ledger.cupAt star.column owner).1 ∩
        joint.saturation.capAt star.column = {owner.1} ∧
      Disjoint (ledger.cupAt star.column owner).1
        (joint.saturation.capAt foreignOne) ∧
      Disjoint (ledger.cupAt star.column owner).1
        (joint.saturation.capAt foreignTwo)

/-- Four private owners together with the six disjoint cap columns force a
full plateau row and two foreign cap blocks avoided by that row. -/
theorem MinimumColumnPrivateResidualStar578.exists_plateauTwoForeignCaps_of_noStrongEight
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    (star : MinimumColumnPrivateResidualStar578 ledger minimum)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    MinimumColumnPlateauTwoForeignCaps578 ledger minimum star := by
  classical
  let base := matrix.cell minimum.row minimum.column
  have hsourceMem
      (c : {x : Fin n // x ∈ joint.saturation.capAt star.column}) :
      c.1 ∈ (ledger.cupAt star.column c).1 := by
    have hmem : c.1 ∈
        (ledger.cupAt star.column c).1 ∩
          joint.saturation.capAt star.column := by
      rw [star.deletion_inter c]
      simp
    exact (Finset.mem_inter.mp hmem).1
  have hplateau : ∃ c, ∀ j,
      (matrix.cell (ledger.cupAt star.column c) j).path = base.path := by
    rcases minimum.oneSided_of_noStrongEight hnoStrong with hright | hleft
    · by_contra hnone
      push Not at hnone
      have hrowUpper
          (c : {x : Fin n // x ∈ joint.saturation.capAt star.column}) :
          (ledger.cupAt star.column c).1 ⊆ base.node.upper := by
        obtain ⟨j, hj⟩ := hnone c
        rcases hright (ledger.cupAt star.column c) j with
          hbase | ⟨tail, hstrict⟩
        · exact (hj hbase).elim
        · exact Finset.subset_union_left.trans
            (minimum.cell_union_subset_upper_of_extends hstrict)
      have hcapUpper : joint.saturation.capAt star.column ⊆
          base.node.upper := by
        intro x hx
        exact hrowUpper ⟨x, hx⟩ (hsourceMem ⟨x, hx⟩)
      have hcapCard := (mem_capWitnesses.mp
        (joint.saturation.capAt_mem star.column)).2.1
      obtain ⟨x, hx⟩ : (joint.saturation.capAt star.column).Nonempty :=
        Finset.card_pos.mp (by omega)
      let c : {x : Fin n // x ∈ joint.saturation.capAt star.column} := ⟨x, hx⟩
      let cell := matrix.cell (ledger.cupAt star.column c) star.column
      have hpath : cell.path = base.path := star.all_base _
      have hnode : cell.node = base.node := by
        have hlookup := cell.lookup
        rw [hpath, base.lookup] at hlookup
        exact (Option.some.inj hlookup).symm
      apply cell.not_all_upper
      rw [hnode]
      exact Finset.union_subset (hrowUpper c) hcapUpper
    · by_contra hnone
      push Not at hnone
      have hrowLower
          (c : {x : Fin n // x ∈ joint.saturation.capAt star.column}) :
          (ledger.cupAt star.column c).1 ⊆ base.node.lower := by
        obtain ⟨j, hj⟩ := hnone c
        rcases hleft (ledger.cupAt star.column c) j with
          hbase | ⟨tail, hstrict⟩
        · exact (hj hbase).elim
        · exact Finset.subset_union_left.trans
            (minimum.cell_union_subset_lower_of_extends hstrict)
      have hcapLower : joint.saturation.capAt star.column ⊆
          base.node.lower := by
        intro x hx
        exact hrowLower ⟨x, hx⟩ (hsourceMem ⟨x, hx⟩)
      have hcapCard := (mem_capWitnesses.mp
        (joint.saturation.capAt_mem star.column)).2.1
      obtain ⟨x, hx⟩ : (joint.saturation.capAt star.column).Nonempty :=
        Finset.card_pos.mp (by omega)
      let c : {x : Fin n // x ∈ joint.saturation.capAt star.column} := ⟨x, hx⟩
      let cell := matrix.cell (ledger.cupAt star.column c) star.column
      have hpath : cell.path = base.path := star.all_base _
      have hnode : cell.node = base.node := by
        have hlookup := cell.lookup
        rw [hpath, base.lookup] at hlookup
        exact (Option.some.inj hlookup).symm
      apply cell.not_all_lower
      rw [hnode]
      exact Finset.union_subset (hrowLower c) hcapLower
  obtain ⟨source, hrow⟩ := hplateau
  have hcupData := mem_capWitnesses.mp
    (joint.ledger.mem_residualCupFamily.mp
      (ledger.cupAt star.column source).2).1
  obtain ⟨foreign₁, foreign₂, hforeignNe, hdisjoint₁, hdisjoint₂⟩ :=
    exists_two_disjoint_capAt578_of_card_le_four joint.saturation
      (vertices := (ledger.cupAt star.column source).1) (by omega)
  have hforeign₁Source : foreign₁ ≠ star.column := by
    intro heq
    subst foreign₁
    exact star.hits_all (ledger.cupAt star.column source) hdisjoint₁
  have hforeign₂Source : foreign₂ ≠ star.column := by
    intro heq
    subst foreign₂
    exact star.hits_all (ledger.cupAt star.column source) hdisjoint₂
  exact ⟨source, foreign₁, foreign₂, hforeignNe,
    hforeign₁Source, hforeign₂Source, by simpa [base] using hrow,
    star.deletion_inter source, hdisjoint₁, hdisjoint₂⟩

end ErdosSzekeres

end
