module

public import ErdosSzekeres.PredecessorHalfFin15SharedAnchor

@[expose] public section

namespace ErdosSzekeres

/-- The defect forced by a shared four-point blocker uses exactly two vertices
of that blocker in addition to the two exterior vertices. -/
theorem predecessorHalfFin15_sharedAnchor_singleEndDefect_twoBase
    (χ : TripleColoring 15)
    (hone : OneChangeOn χ Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6)
    {support base : Finset (Fin 15)} {q r : Fin 15}
    (hbaseSub : base ⊆ support)
    (hbaseCard : base.card = 4)
    (hqOutside : q ∈ Finset.univ \ support)
    (hrOutside : r ∈ Finset.univ \ support)
    (hqr : q ≠ r)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base)) :
    ∃ i j k l : Fin 15, ∃ (hij : i < j) (hjk : j < k) (hkl : k < l),
      i ∈ insert q (insert r base) ∧
      j ∈ insert q (insert r base) ∧
      k ∈ insert q (insert r base) ∧
      l ∈ insert q (insert r base) ∧
      (q = i ∨ q = j ∨ q = k ∨ q = l) ∧
      (r = i ∨ r = j ∨ r = k ∨ r = l) ∧
      (({i, j, k, l} : Finset (Fin 15)) ∩ base).card = 2 ∧
      ((χ ⟨i, j, k, hij, hjk⟩ =
              χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ ≠
              χ ⟨j, k, l, hjk, hkl⟩) ∨
        (χ ⟨i, j, k, hij, hjk⟩ ≠
              χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
              χ ⟨j, k, l, hjk, hkl⟩)) := by
  classical
  obtain ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl,
      hqOccurs, hrOccurs, hsingle⟩ :=
    predecessorHalfFin15_sharedAnchor_singleEndDefect χ hone hnoStrong
      hbaseSub hbaseCard hqOutside hrOutside hqr hqStrong hrStrong
  let quad : Finset (Fin 15) := {i, j, k, l}
  have hquadCard : quad.card = 4 := by
    simp [quad, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt ((hij.trans hjk).trans hkl)]
  have hquadSub : quad ⊆ insert q (insert r base) := by
    intro x hx
    simp only [quad, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
    · exact hl
  have hqQuad : q ∈ quad := by
    simpa only [quad, Finset.mem_insert, Finset.mem_singleton] using hqOccurs
  have hrQuad : r ∈ quad := by
    simpa only [quad, Finset.mem_insert, Finset.mem_singleton] using hrOccurs
  have hqNotBase : q ∉ base := fun hq ↦
    (Finset.mem_sdiff.mp hqOutside).2 (hbaseSub hq)
  have hrNotBase : r ∉ base := fun hr ↦
    (Finset.mem_sdiff.mp hrOutside).2 (hbaseSub hr)
  have hquadDiff : quad \ base = {q, r} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      rcases Finset.mem_insert.mp (hquadSub hx.1) with hq | hrest
      · exact Or.inl hq
      · rcases Finset.mem_insert.mp hrest with hr | hbase
        · exact Or.inr hr
        · exact (hx.2 hbase).elim
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨hqQuad, hqNotBase⟩
      · exact ⟨hrQuad, hrNotBase⟩
  have hquadDiffCard : (quad \ base).card = 2 := by
    rw [hquadDiff]
    simp [hqr]
  have hinterCard : (quad ∩ base).card = 2 := by
    have hpartition := Finset.card_sdiff_add_card_inter quad base
    omega
  exact ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl,
    hqOccurs, hrOccurs, by simpa [quad] using hinterCard, hsingle⟩

end ErdosSzekeres

end
