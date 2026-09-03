module

public import ErdosSzekeres.PredecessorHalfFin15SharedAnchorGlobal

@[expose] public section

/-!
# Cross-exterior extension for the Fin15 Fano branch

This module isolates the multi-owner outcome of the three-exterior Fano
transversal witness.  Its target is an unconditional singleton extension of
the resulting strong five-set; the no-strong-six assumption enters only in
the final consumer.
-/

namespace ErdosSzekeres

/-- The four multi-owner alternatives in the exact three-exterior witness. -/
def Fin15ThreeExteriorMultiOwnerWitness
    (chi : TripleColoring 15) (support : Finset (Fin 15))
    (q r s x y : Fin 15) : Prop :=
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase x).erase y ∧ residue.card = 2 ∧
      IsStrongPolygonSet chi (insert q (insert r (insert s residue)))) ∨
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert q (insert r residue))) ∨
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert q (insert s residue))) ∨
  ∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert r (insert s residue))

/-- A common-anchor multi-owner conclusion can choose its two support
erasures after choosing the residue.  The resulting double-erased candidate
contains the same multi-owner strong five and erases at least one point of the
common four-base. -/
theorem fin15_commonAnchor_multiOwner_adaptiveDoubleErase
    (chi : TripleColoring 15)
    {support base : Finset (Fin 15)} {q r s : Fin 15}
    (hsupportCard : support.card = 7)
    (hbaseSub : base ⊆ support) (hbaseCard : base.card = 4)
    (hclosure :
      (∃ residue : Finset (Fin 15),
        residue ⊆ base ∧ residue.card = 2 ∧
          IsStrongPolygonSet chi (insert q (insert r (insert s residue)))) ∨
      (∃ residue : Finset (Fin 15),
        residue ⊆ base ∧ residue.card = 3 ∧
          IsStrongPolygonSet chi (insert q (insert r residue))) ∨
      (∃ residue : Finset (Fin 15),
        residue ⊆ base ∧ residue.card = 3 ∧
          IsStrongPolygonSet chi (insert q (insert s residue))) ∨
      ∃ residue : Finset (Fin 15),
        residue ⊆ base ∧ residue.card = 3 ∧
          IsStrongPolygonSet chi (insert r (insert s residue))) :
    ∃ x ∈ support, ∃ y ∈ support, x ≠ y ∧
      ¬base ⊆ (support.erase x).erase y ∧
      Fin15ThreeExteriorMultiOwnerWitness chi support q r s x y := by
  classical
  have adaptTwo (residue : Finset (Fin 15))
      (hresidueSub : residue ⊆ base) (hresidueCard : residue.card = 2) :
      ∃ x ∈ support, ∃ y ∈ support, x ≠ y ∧
        ¬base ⊆ (support.erase x).erase y ∧
        residue ⊆ (support.erase x).erase y := by
    have hdiffCard : (base \ residue).card = 2 := by
      rw [Finset.card_sdiff_of_subset hresidueSub, hbaseCard, hresidueCard]
    obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffCard
    have hxDiff : x ∈ base \ residue := by rw [hdiff]; simp
    have hyDiff : y ∈ base \ residue := by rw [hdiff]; simp
    have hxBase : x ∈ base := (Finset.mem_sdiff.mp hxDiff).1
    have hyBase : y ∈ base := (Finset.mem_sdiff.mp hyDiff).1
    have hxNotResidue : x ∉ residue := (Finset.mem_sdiff.mp hxDiff).2
    have hyNotResidue : y ∉ residue := (Finset.mem_sdiff.mp hyDiff).2
    have hxSupport : x ∈ support := hbaseSub hxBase
    have hySupport : y ∈ support := hbaseSub hyBase
    have hresidueDouble : residue ⊆ (support.erase x).erase y := by
      intro z hz
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hbaseSub (hresidueSub hz)⟩⟩
      · intro hzy
        exact hyNotResidue (hzy ▸ hz)
      · intro hzx
        exact hxNotResidue (hzx ▸ hz)
    have hbaseKilled : ¬base ⊆ (support.erase x).erase y := by
      intro hsub
      have hxDouble := hsub hxBase
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hxDouble).2).1 rfl
    exact ⟨x, hxSupport, y, hySupport, hxy, hbaseKilled, hresidueDouble⟩
  have adaptThree (residue : Finset (Fin 15))
      (hresidueSub : residue ⊆ base) (hresidueCard : residue.card = 3) :
      ∃ x ∈ support, ∃ y ∈ support, x ≠ y ∧
        ¬base ⊆ (support.erase x).erase y ∧
        residue ⊆ (support.erase x).erase y := by
    have hdiffCard : (base \ residue).card = 1 := by
      rw [Finset.card_sdiff_of_subset hresidueSub, hbaseCard, hresidueCard]
    obtain ⟨x, hdiff⟩ := Finset.card_eq_one.mp hdiffCard
    have hxDiff : x ∈ base \ residue := by rw [hdiff]; simp
    have hxBase : x ∈ base := (Finset.mem_sdiff.mp hxDiff).1
    have hxNotResidue : x ∉ residue := (Finset.mem_sdiff.mp hxDiff).2
    have houtsideCard : (support \ base).card = 3 := by
      rw [Finset.card_sdiff_of_subset hbaseSub, hsupportCard, hbaseCard]
    have houtsideNonempty : (support \ base).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨y, hyOutside⟩ := houtsideNonempty
    have hySupport : y ∈ support := (Finset.mem_sdiff.mp hyOutside).1
    have hyNotBase : y ∉ base := (Finset.mem_sdiff.mp hyOutside).2
    have hxSupport : x ∈ support := hbaseSub hxBase
    have hxy : x ≠ y := by
      intro hxy
      exact hyNotBase (hxy ▸ hxBase)
    have hresidueDouble : residue ⊆ (support.erase x).erase y := by
      intro z hz
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hbaseSub (hresidueSub hz)⟩⟩
      · intro hzy
        exact hyNotBase (hzy ▸ hresidueSub hz)
      · intro hzx
        exact hxNotResidue (hzx ▸ hz)
    have hbaseKilled : ¬base ⊆ (support.erase x).erase y := by
      intro hsub
      have hxDouble := hsub hxBase
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hxDouble).2).1 rfl
    exact ⟨x, hxSupport, y, hySupport, hxy, hbaseKilled, hresidueDouble⟩
  rcases hclosure with hqrs | hqr | hqs | hrs
  · obtain ⟨residue, hresidueSub, hresidueCard, hstrong⟩ := hqrs
    obtain ⟨x, hx, y, hy, hxy, hkilled, hresidueDouble⟩ :=
      adaptTwo residue hresidueSub hresidueCard
    exact ⟨x, hx, y, hy, hxy, hkilled, Or.inl
      ⟨residue, hresidueDouble, hresidueCard, hstrong⟩⟩
  · obtain ⟨residue, hresidueSub, hresidueCard, hstrong⟩ := hqr
    obtain ⟨x, hx, y, hy, hxy, hkilled, hresidueDouble⟩ :=
      adaptThree residue hresidueSub hresidueCard
    exact ⟨x, hx, y, hy, hxy, hkilled, Or.inr (Or.inl
      ⟨residue, hresidueDouble, hresidueCard, hstrong⟩)⟩
  · obtain ⟨residue, hresidueSub, hresidueCard, hstrong⟩ := hqs
    obtain ⟨x, hx, y, hy, hxy, hkilled, hresidueDouble⟩ :=
      adaptThree residue hresidueSub hresidueCard
    exact ⟨x, hx, y, hy, hxy, hkilled, Or.inr (Or.inr (Or.inl
      ⟨residue, hresidueDouble, hresidueCard, hstrong⟩))⟩
  · obtain ⟨residue, hresidueSub, hresidueCard, hstrong⟩ := hrs
    obtain ⟨x, hx, y, hy, hxy, hkilled, hresidueDouble⟩ :=
      adaptThree residue hresidueSub hresidueCard
    exact ⟨x, hx, y, hy, hxy, hkilled, Or.inr (Or.inr (Or.inr
      ⟨residue, hresidueDouble, hresidueCard, hstrong⟩))⟩

/-
The two frozen theorem declarations cannot be elaborated.  Their primary
signature binds

  {support blocks first second third : Finset (Fin 15)}

but then treats `blocks` as a collection of four-sets in `hblockSub`,
`hblockCard`, `hfano`, and the three membership premises.  Lean consequently
infers the quantified `block` in `hblockSub` as a `Fin 15`, making
`block ⊆ support` ill-typed.  Because the task freezes the theorem statement,
this module records only the independently well-typed frozen definition at
the bounded-stop terminal.  No corrected theorem has been substituted.
-/

end ErdosSzekeres

end
