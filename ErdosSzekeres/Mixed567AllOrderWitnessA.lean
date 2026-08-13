module

public import ErdosSzekeres.Mixed567AllOrderLabel

@[expose] public section

/-! The two A-witness reconstructions, isolated from the other four witnesses. -/

namespace ErdosSzekeres

private theorem witness_reconstruct_A {n : ℕ}
    {first second third : Finset (Fin n)}
    (hsub : third ⊆ first ∪ second) :
    third = (first \ (first \ third)) ∪ (second \ (second \ third)) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp (hsub hx) with hxFirst | hxSecond
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
        ⟨hxFirst, fun hdiff ↦ (Finset.mem_sdiff.mp hdiff).2 hx⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr
        ⟨hxSecond, fun hdiff ↦ (Finset.mem_sdiff.mp hdiff).2 hx⟩))
  · intro hx
    rcases Finset.mem_union.mp hx with hxFirst | hxSecond
    · have hdata := Finset.mem_sdiff.mp hxFirst
      by_contra hxThird
      exact hdata.2 (Finset.mem_sdiff.mpr ⟨hdata.1, hxThird⟩)
    · have hdata := Finset.mem_sdiff.mp hxSecond
      by_contra hxThird
      exact hdata.2 (Finset.mem_sdiff.mpr ⟨hdata.1, hxThird⟩)

private theorem erase_erase_comm_A {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : α) :
    (s.erase a).erase b = (s.erase b).erase a := by
  ext x
  simp only [Finset.mem_erase]
  tauto

private theorem singleton_union_six_A {α : Type*} [DecidableEq α]
    (a b c d e f : α) :
    ({a} : Finset α) ∪ {b, c, d, e, f} = {a, b, c, d, e, f} := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

/-- The A0/A1 canonical images are witnesses for the packaged labelling. -/
theorem shortFirstMixed567WitnessA {n : ℕ} {χ : TripleColoring n}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem : IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (data : Mixed567ShortFirstData first second witnesses) :
    mixed567A0.image data.embed ∈ witnesses ∧
      mixed567A1.image data.embed ∈ witnesses := by
  classical
  have hdEraseC : data.d ∈ second.erase data.c :=
    Finset.mem_erase.mpr ⟨data.hcd.symm, data.hd⟩
  have hcEraseD : data.c ∈ second.erase data.d :=
    Finset.mem_erase.mpr ⟨data.hcd, data.hc⟩
  have hA0 : data.A0 =
      {data.p, data.d, data.e0, data.e1, data.e2, data.e3} := by
    rw [witness_reconstruct_A (hsystem.1 data.A0 data.A0_mem).2.2.1,
      data.hA0First, data.hA0Second]
    rw [Finset.sdiff_erase_self data.hp, Finset.sdiff_singleton_eq_erase,
      ← Finset.insert_erase hdEraseC, data.hE]
    exact singleton_union_six_A data.p data.d data.e0 data.e1 data.e2 data.e3
  have hA1 : data.A1 =
      {data.q, data.c, data.e0, data.e1, data.e2, data.e3} := by
    rw [witness_reconstruct_A (hsystem.1 data.A1 data.A1_mem).2.2.1,
      data.hA1First, data.hA1Second]
    rw [Finset.sdiff_erase_self data.hq, Finset.sdiff_singleton_eq_erase,
      ← Finset.insert_erase hcEraseD,
      erase_erase_comm_A second data.d data.c, data.hE]
    exact singleton_union_six_A data.q data.c data.e0 data.e1 data.e2 data.e3
  have hA0Image : mixed567A0.image data.embed = data.A0 := by
    rw [hA0]
    ext x
    simp [mixed567A0, Mixed567ShortFirstData.embed, mixed567Map]
  have hA1Image : mixed567A1.image data.embed = data.A1 := by
    rw [hA1]
    ext x
    simp [mixed567A1, Mixed567ShortFirstData.embed, mixed567Map]
  exact ⟨by simpa [hA0Image] using data.A0_mem,
    by simpa [hA1Image] using data.A1_mem⟩

end ErdosSzekeres

end
