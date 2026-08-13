module

public import ErdosSzekeres.Mixed567AllOrderLabel

@[expose] public section

/-! The two B-witness reconstructions, isolated from the other four witnesses. -/

namespace ErdosSzekeres

private theorem witness_reconstruct_B {n : ℕ}
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

private theorem erase_erase_comm_B {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : α) :
    (s.erase a).erase b = (s.erase b).erase a := by
  ext x
  simp only [Finset.mem_erase]
  tauto

/-- The B0/B1 canonical images are witnesses for the packaged labelling. -/
theorem shortFirstMixed567WitnessB {n : ℕ} {χ : TripleColoring n}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem : IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (data : Mixed567ShortFirstData first second witnesses) :
    mixed567B0.image data.embed ∈ witnesses ∧
      mixed567B1.image data.embed ∈ witnesses := by
  classical
  have hqEraseP : data.q ∈ first.erase data.p :=
    Finset.mem_erase.mpr ⟨data.hpq.symm, data.hq⟩
  have hpEraseQ : data.p ∈ first.erase data.q :=
    Finset.mem_erase.mpr ⟨data.hpq, data.hp⟩
  have hB0 : data.B0 =
      {data.q, data.u0, data.u1, data.v0, data.v1, data.d} := by
    rw [witness_reconstruct_B (hsystem.1 data.B0 data.B0_mem).2.2.1,
      data.hB0First, data.hB0Second]
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_erase_self data.hd,
      ← Finset.insert_erase hqEraseP, ← data.hPQ, data.hP, data.hQ]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hB1 : data.B1 =
      {data.p, data.u0, data.u1, data.v0, data.v1, data.c} := by
    rw [witness_reconstruct_B (hsystem.1 data.B1 data.B1_mem).2.2.1,
      data.hB1First, data.hB1Second]
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_erase_self data.hc,
      ← Finset.insert_erase hpEraseQ,
      erase_erase_comm_B first data.q data.p,
      ← data.hPQ, data.hP, data.hQ]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hB0Image : mixed567B0.image data.embed = data.B0 := by
    rw [hB0]
    ext x
    simp [mixed567B0, Mixed567ShortFirstData.embed, mixed567Map]
  have hB1Image : mixed567B1.image data.embed = data.B1 := by
    rw [hB1]
    ext x
    simp [mixed567B1, Mixed567ShortFirstData.embed, mixed567Map]
  exact ⟨by simpa [hB0Image] using data.B0_mem,
    by simpa [hB1Image] using data.B1_mem⟩

end ErdosSzekeres

end
