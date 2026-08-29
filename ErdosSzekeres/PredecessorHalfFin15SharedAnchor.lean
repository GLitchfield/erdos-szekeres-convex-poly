module

public import ErdosSzekeres.PredecessorHalfFin15Obstruction

@[expose] public section

/-!
# Shared-anchor defects at fifteen points

When two exterior vertices use the same four-point blocker, their six-point
union cannot be strong in the target-free branch.  Since deleting either
exterior vertex leaves a strong five-set, every witnessing quadruple contains
both exterior vertices.  The one-change law then says exactly one end of the
strong-polygon equality fails.
-/

namespace ErdosSzekeres

/-- Failure of middle determinacy is witnessed on one ordered quadruple. -/
theorem exists_defect_quadruple_of_not_isStrongPolygonSet
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hnot : ¬IsStrongPolygonSet χ s) :
    ∃ i j k l : Fin n, ∃ (hij : i < j) (hjk : j < k) (hkl : k < l),
      i ∈ s ∧ j ∈ s ∧ k ∈ s ∧ l ∈ s ∧
        ¬(χ ⟨i, j, k, hij, hjk⟩ =
              χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
              χ ⟨j, k, l, hjk, hkl⟩) := by
  classical
  unfold IsStrongPolygonSet at hnot
  push Not at hnot
  obtain ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl, hdefect⟩ := hnot
  exact ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl,
    fun hboth ↦ hdefect hboth.1 hboth.2⟩

/-- If two one-vertex extensions of a common base are strong but their union
is not, every defect quadruple can be chosen to contain both new vertices. -/
theorem exists_sharedExtension_defect_containing_both
    {n : ℕ} {χ : TripleColoring n} {base : Finset (Fin n)}
    {q r : Fin n}
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base))
    (hnot : ¬IsStrongPolygonSet χ (insert q (insert r base))) :
    ∃ i j k l : Fin n, ∃ (hij : i < j) (hjk : j < k) (hkl : k < l),
      i ∈ insert q (insert r base) ∧
      j ∈ insert q (insert r base) ∧
      k ∈ insert q (insert r base) ∧
      l ∈ insert q (insert r base) ∧
      (q = i ∨ q = j ∨ q = k ∨ q = l) ∧
      (r = i ∨ r = j ∨ r = k ∨ r = l) ∧
        ¬(χ ⟨i, j, k, hij, hjk⟩ =
              χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
              χ ⟨j, k, l, hjk, hkl⟩) := by
  obtain ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl, hdefect⟩ :=
    exists_defect_quadruple_of_not_isStrongPolygonSet hnot
  have hqOccurs : q = i ∨ q = j ∨ q = k ∨ q = l := by
    by_contra hqAbsent
    push Not at hqAbsent
    apply hdefect
    apply hrStrong hij hjk hkl
    · exact (Finset.mem_insert.mp hi).resolve_left hqAbsent.1.symm
    · exact (Finset.mem_insert.mp hj).resolve_left hqAbsent.2.1.symm
    · exact (Finset.mem_insert.mp hk).resolve_left hqAbsent.2.2.1.symm
    · exact (Finset.mem_insert.mp hl).resolve_left hqAbsent.2.2.2.symm
  have hrOccurs : r = i ∨ r = j ∨ r = k ∨ r = l := by
    by_contra hrAbsent
    push Not at hrAbsent
    apply hdefect
    apply hqStrong hij hjk hkl
    · rcases Finset.mem_insert.mp hi with hiq | hi
      · exact Finset.mem_insert.mpr (Or.inl hiq)
      · exact Finset.mem_insert_of_mem
          ((Finset.mem_insert.mp hi).resolve_left hrAbsent.1.symm)
    · rcases Finset.mem_insert.mp hj with hjq | hj
      · exact Finset.mem_insert.mpr (Or.inl hjq)
      · exact Finset.mem_insert_of_mem
          ((Finset.mem_insert.mp hj).resolve_left hrAbsent.2.1.symm)
    · rcases Finset.mem_insert.mp hk with hkq | hk
      · exact Finset.mem_insert.mpr (Or.inl hkq)
      · exact Finset.mem_insert_of_mem
          ((Finset.mem_insert.mp hk).resolve_left hrAbsent.2.2.1.symm)
    · rcases Finset.mem_insert.mp hl with hlq | hl
      · exact Finset.mem_insert.mpr (Or.inl hlq)
      · exact Finset.mem_insert_of_mem
          ((Finset.mem_insert.mp hl).resolve_left hrAbsent.2.2.2.symm)
  exact ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl,
    hqOccurs, hrOccurs, hdefect⟩

/-- An allowed four-word which fails the strong law has exactly one failed
end equality. -/
theorem TurnSequenceAllowed.single_end_failure_of_not_strong
    {a b c d : Turn} (hallowed : TurnSequenceAllowed a b c d)
    (hnot : ¬(a = b ∧ c = d)) :
    (a = b ∧ c ≠ d) ∨ (a ≠ b ∧ c = d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [TurnSequenceAllowed]

/-- One-change sharpens a shared-extension defect to a single failed end
equality while preserving the fact that both new vertices occur. -/
theorem exists_sharedExtension_oneChange_defect_containing_both
    {n : ℕ} {χ : TripleColoring n} {ambient base : Finset (Fin n)}
    {q r : Fin n}
    (hunionSub : insert q (insert r base) ⊆ ambient)
    (hone : OneChangeOn χ ambient)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base))
    (hnot : ¬IsStrongPolygonSet χ (insert q (insert r base))) :
    ∃ i j k l : Fin n, ∃ (hij : i < j) (hjk : j < k) (hkl : k < l),
      i ∈ insert q (insert r base) ∧
      j ∈ insert q (insert r base) ∧
      k ∈ insert q (insert r base) ∧
      l ∈ insert q (insert r base) ∧
      (q = i ∨ q = j ∨ q = k ∨ q = l) ∧
      (r = i ∨ r = j ∨ r = k ∨ r = l) ∧
      ((χ ⟨i, j, k, hij, hjk⟩ =
              χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ ≠
              χ ⟨j, k, l, hjk, hkl⟩) ∨
        (χ ⟨i, j, k, hij, hjk⟩ ≠
              χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
              χ ⟨j, k, l, hjk, hkl⟩)) := by
  obtain ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl,
      hqOccurs, hrOccurs, hdefect⟩ :=
    exists_sharedExtension_defect_containing_both hqStrong hrStrong hnot
  have hallowed := hone hij hjk hkl
    (hunionSub hi) (hunionSub hj) (hunionSub hk) (hunionSub hl)
  exact ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl,
    hqOccurs, hrOccurs,
    hallowed.single_end_failure_of_not_strong hdefect⟩

/-- In the Fin15 target-free branch, a shared four-point blocker has a
single-end defect quadruple containing both exterior vertices. -/
theorem predecessorHalfFin15_sharedAnchor_singleEndDefect
    (χ : TripleColoring 15)
    (hone : OneChangeOn χ Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6)
    {support base : Finset (Fin 15)} {q r : Fin 15}
    (hbaseSub : base ⊆ support) (hbaseCard : base.card = 4)
    (hqOutside : q ∈ Finset.univ \ support)
    (hrOutside : r ∈ Finset.univ \ support) (hqr : q ≠ r)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base)) :
    ∃ i j k l : Fin 15, ∃ (hij : i < j) (hjk : j < k) (hkl : k < l),
      i ∈ insert q (insert r base) ∧
      j ∈ insert q (insert r base) ∧
      k ∈ insert q (insert r base) ∧
      l ∈ insert q (insert r base) ∧
      (q = i ∨ q = j ∨ q = k ∨ q = l) ∧
      (r = i ∨ r = j ∨ r = k ∨ r = l) ∧
      ((χ ⟨i, j, k, hij, hjk⟩ =
              χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ ≠
              χ ⟨j, k, l, hjk, hkl⟩) ∨
        (χ ⟨i, j, k, hij, hjk⟩ ≠
              χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
              χ ⟨j, k, l, hjk, hkl⟩)) := by
  have hqNotSupport := (Finset.mem_sdiff.mp hqOutside).2
  have hrNotSupport := (Finset.mem_sdiff.mp hrOutside).2
  have hqNotBase : q ∉ base := fun hq ↦ hqNotSupport (hbaseSub hq)
  have hrNotBase : r ∉ base := fun hr ↦ hrNotSupport (hbaseSub hr)
  have hqNotInsert : q ∉ insert r base := by
    simp [hqr, hqNotBase]
  have hunionCard : (insert q (insert r base)).card = 6 := by
    rw [Finset.card_insert_of_notMem hqNotInsert,
      Finset.card_insert_of_notMem hrNotBase, hbaseCard]
  have hnotUnion : ¬IsStrongPolygonSet χ (insert q (insert r base)) := by
    intro hstrong
    exact hnoStrong ⟨insert q (insert r base), Finset.subset_univ _,
      hunionCard, hstrong⟩
  exact exists_sharedExtension_oneChange_defect_containing_both
    (Finset.subset_univ _) hone hqStrong hrStrong hnotUnion

end ErdosSzekeres

end
