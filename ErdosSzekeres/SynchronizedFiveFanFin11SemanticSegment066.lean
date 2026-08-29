module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment065

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 066. -/

theorem synchronizedFiveFanFin11Semantic_clause04753 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1467 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0574 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0574 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1467 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04754 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1467 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1467 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1795 chi).mpr
  have hright0 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨8, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04755 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0575 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0202 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0575 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0061,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04756 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0575 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0203 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0575 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0061,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04757 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0575 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0575 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0061,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04758 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0575 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0230 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0575 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0061,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04759 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0575 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0575 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0061,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04760 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0575 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0575 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0061,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04761 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0575 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0575 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1027 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04762 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0575 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1027 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0575 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1027 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0061 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause04763 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1468 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0575 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0575 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1468 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04764 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0202 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0093,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04765 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0204 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0093,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04766 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0093,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04767 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0093,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04768 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0369 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0093,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04769 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0576 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1028 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04770 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1028 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0093 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04771 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1028 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1028 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0093 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause04772 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1028 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1028 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0093 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause04773 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1028 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1028 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0093 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause04774 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1469 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0576 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1469 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04775 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0576 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1469 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0576 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1469 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0093 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause04776 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0577 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0202 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0577 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0157,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04777 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0577 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0205 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0205 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0577 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0157,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04778 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0577 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0211 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0577 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0157,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04779 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0577 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0232 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0232 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0577 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0157,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04780 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0577 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0370 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0577 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0157,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04781 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0577 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0577 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1029 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04782 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1470 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0577 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0577 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1470 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04783 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0578 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0202 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0578 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0285,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04784 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0578 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0206 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0578 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0285,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04785 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0578 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0212 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0578 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0285,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04786 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0578 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0233 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0578 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0285,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04787 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0578 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0578 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0285,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04788 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0578 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0578 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1030 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04789 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1471 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0578 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0578 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1471 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04790 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0578 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0578 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1471 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0285 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause04791 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0202 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0579 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0541,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04792 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0207 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0579 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0541,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04793 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0213 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0579 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0541,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04794 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0234 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0579 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0541,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04795 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0579 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0541,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04796 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0579 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0579 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0541,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04797 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0579 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0579 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1031 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04798 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1472 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0579 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0579 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1472 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04799 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0579 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0579 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1472 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0541 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause04800 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0202 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0580 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1053,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04801 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0208 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0580 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1053,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04802 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0580 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1053,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04803 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0235 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0580 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1053,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04804 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0373 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0580 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1053,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04805 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0580 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0580 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1032 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04806 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1473 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0580 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0580 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1473 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04807 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0581 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0203 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0581 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04808 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0581 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0204 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0581 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04809 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0581 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0215 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0581 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04810 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0581 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0236 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0581 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04811 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0581 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0581 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04812 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0581 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0581 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1033 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04813 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0581 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1033 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0581 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1033 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0109 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause04814 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1474 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0581 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0581 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1474 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04815 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1474 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1474 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0109 chi).mpr
  have hright0 : chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04816 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0581 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1474 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0581 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1474 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0109 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause04817 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0582 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0203 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0582 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04818 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0582 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0205 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0205 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0582 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04819 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0582 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0582 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04820 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0582 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0237 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0237 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0582 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04821 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0582 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0375 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0582 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04822 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0582 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0582 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1034 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04823 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1475 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0582 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0582 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1475 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04824 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0583 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0203 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0583 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0301,
  ] at hbad
  tauto

end ErdosSzekeres

end
