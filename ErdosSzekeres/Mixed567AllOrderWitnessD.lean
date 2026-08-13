module

public import ErdosSzekeres.Mixed567AllOrderLabel

@[expose] public section

/-! The two D-witness reconstructions, isolated from the other four witnesses. -/

namespace ErdosSzekeres

private theorem witness_reconstruct_D {n : ℕ}
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

private theorem carrier_sdiff_partition_left_D {n : ℕ}
    {first P Q : Finset (Fin n)} {p q : Fin n}
    (hp : p ∈ first) (hq : q ∈ first) (hpq : p ≠ q)
    (hdisjoint : Disjoint P Q) (hPQ : P ∪ Q = (first.erase p).erase q) :
    first \ P = {p, q} ∪ Q := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  have hcharacterize : x ∈ P ∨ x ∈ Q ↔
      x ∈ first ∧ x ≠ p ∧ x ≠ q := by
    rw [← Finset.mem_union, hPQ]
    simp only [Finset.mem_erase]
    tauto
  have hPQDisjoint : x ∈ P → x ∈ Q → False := by
    intro hxP hxQ
    exact (Finset.disjoint_left.mp hdisjoint) hxP hxQ
  constructor
  · rintro ⟨hxFirst, hxNotP⟩
    by_cases hxp : x = p
    · exact Or.inl (Or.inl hxp)
    by_cases hxq : x = q
    · exact Or.inl (Or.inr hxq)
    exact Or.inr ((hcharacterize.mpr ⟨hxFirst, hxp, hxq⟩).resolve_left hxNotP)
  · rintro ((rfl | rfl) | hxQ)
    · refine ⟨hp, ?_⟩
      intro hpP
      exact (hcharacterize.mp (Or.inl hpP)).2.1 rfl
    · refine ⟨hq, ?_⟩
      intro hqP
      exact (hcharacterize.mp (Or.inl hqP)).2.2 rfl
    · have hxData := hcharacterize.mp (Or.inr hxQ)
      exact ⟨hxData.1, fun hxP ↦ hPQDisjoint hxP hxQ⟩

private theorem carrier_sdiff_partition_right_D {n : ℕ}
    {first P Q : Finset (Fin n)} {p q : Fin n}
    (hp : p ∈ first) (hq : q ∈ first) (hpq : p ≠ q)
    (hdisjoint : Disjoint P Q) (hPQ : P ∪ Q = (first.erase p).erase q) :
    first \ Q = {p, q} ∪ P := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  have hcharacterize : x ∈ P ∨ x ∈ Q ↔
      x ∈ first ∧ x ≠ p ∧ x ≠ q := by
    rw [← Finset.mem_union, hPQ]
    simp only [Finset.mem_erase]
    tauto
  have hPQDisjoint : x ∈ P → x ∈ Q → False := by
    intro hxP hxQ
    exact (Finset.disjoint_left.mp hdisjoint) hxP hxQ
  constructor
  · rintro ⟨hxFirst, hxNotQ⟩
    by_cases hxp : x = p
    · exact Or.inl (Or.inl hxp)
    by_cases hxq : x = q
    · exact Or.inl (Or.inr hxq)
    exact Or.inr ((hcharacterize.mpr ⟨hxFirst, hxp, hxq⟩).resolve_right hxNotQ)
  · rintro ((rfl | rfl) | hxP)
    · refine ⟨hp, ?_⟩
      intro hpQ
      exact (hcharacterize.mp (Or.inr hpQ)).2.1 rfl
    · refine ⟨hq, ?_⟩
      intro hqQ
      exact (hcharacterize.mp (Or.inr hqQ)).2.2 rfl
    · have hxData := hcharacterize.mp (Or.inl hxP)
      exact ⟨hxData.1, fun hxQ ↦ hPQDisjoint hxP hxQ⟩

/-- The D0/D1 canonical images are witnesses for the packaged labelling. -/
theorem shortFirstMixed567WitnessD {n : ℕ} {χ : TripleColoring n}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem : IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (data : Mixed567ShortFirstData first second witnesses) :
    mixed567D0.image data.embed ∈ witnesses ∧
      mixed567D1.image data.embed ∈ witnesses := by
  classical
  have hSecondDiff : second \ (second.erase data.c).erase data.d =
      {data.c, data.d} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hxSecond, hx⟩
      by_cases hxd : x = data.d
      · exact Or.inr hxd
      · exact Or.inl (Classical.byContradiction fun hxc ↦
          hx ⟨hxd, hxc, hxSecond⟩)
    · rintro (rfl | rfl)
      · exact ⟨data.hc, fun h ↦ h.2.1 rfl⟩
      · exact ⟨data.hd, fun h ↦ h.1 rfl⟩
  have hD0 : data.D0 =
      {data.p, data.q, data.v0, data.v1, data.c, data.d} := by
    rw [witness_reconstruct_D (hsystem.1 data.D0 data.D0_mem).2.2.1,
      data.hD0First, data.hD0Second]
    rw [carrier_sdiff_partition_left_D data.hp data.hq data.hpq
      data.hPQDisjoint data.hPQ, hSecondDiff, data.hQ]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hD1 : data.D1 =
      {data.p, data.q, data.u0, data.u1, data.c, data.d} := by
    rw [witness_reconstruct_D (hsystem.1 data.D1 data.D1_mem).2.2.1,
      data.hD1First, data.hD1Second]
    rw [carrier_sdiff_partition_right_D data.hp data.hq data.hpq
      data.hPQDisjoint data.hPQ, hSecondDiff, data.hP]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hD0Image : mixed567D0.image data.embed = data.D0 := by
    rw [hD0]
    ext x
    simp [mixed567D0, Mixed567ShortFirstData.embed, mixed567Map]
  have hD1Image : mixed567D1.image data.embed = data.D1 := by
    rw [hD1]
    ext x
    simp [mixed567D1, Mixed567ShortFirstData.embed, mixed567Map]
  exact ⟨by simpa [hD0Image] using data.D0_mem,
    by simpa [hD1Image] using data.D1_mem⟩

end ErdosSzekeres

end
