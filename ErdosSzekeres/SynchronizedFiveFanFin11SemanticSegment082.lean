module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment081

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 082. -/

theorem synchronizedFiveFanFin11Semantic_clause05905 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0719 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0292 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0719 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0118,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05906 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0719 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0719 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0118,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05907 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0719 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0719 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0118,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05908 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0719 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0334 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0719 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0118,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05909 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0719 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0388 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0719 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0118,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05910 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1169 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0719 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0719 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1169 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05911 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1169 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0118 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05912 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1609 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0719 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0719 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1609 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05913 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0719 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1609 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0719 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1609 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0118 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause05914 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0719 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1609 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0719 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1609 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0118 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause05915 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0720 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0292 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0720 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0182,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05916 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0720 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0294 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0720 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0182,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05917 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0720 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0299 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0720 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0182,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05918 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0720 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0335 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0720 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0182,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05919 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0720 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0389 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0720 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0182,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05920 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1170 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0720 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0720 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1170 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05921 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1610 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0720 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0720 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1610 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05922 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0721 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0292 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0721 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0310,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05923 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0721 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0721 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0310,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05924 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0721 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0721 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0310,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05925 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0721 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0721 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0310,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05926 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0721 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0390 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0721 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0310,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05927 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1171 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0721 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0721 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1171 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05928 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1611 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0721 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0721 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1611 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05929 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0722 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0292 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0722 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0566,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05930 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0722 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0296 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0722 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0566,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05931 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0722 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0722 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0566,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05932 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0722 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0722 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0566,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05933 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0722 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0391 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0722 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0566,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05934 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1172 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0722 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0722 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1172 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05935 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1612 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0722 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0722 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1612 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05936 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1612 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1612 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0566 chi).mpr
  have hright0 : chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05937 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0722 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1612 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0722 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1612 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0566 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause05938 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0723 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0292 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0723 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1078,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05939 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0723 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0297 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0723 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1078,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05940 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0723 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0723 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1078,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05941 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0723 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0338 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0723 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1078,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05942 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0723 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0392 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0723 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1078,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05943 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1173 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0723 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0723 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1173 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05944 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0723 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0723 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1173 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1078 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05945 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0723 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0723 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1173 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1078 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause05946 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1613 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0723 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0723 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1613 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05947 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0724 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0724 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0214,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05948 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0724 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0339 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0724 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0214,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05949 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0724 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0393 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0724 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0214,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05950 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1174 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0724 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0724 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1174 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05951 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1614 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0724 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0724 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1614 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05952 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0725 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0725 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0342,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05953 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0725 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0725 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0342,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05954 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0725 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0304 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0725 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0342,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05955 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0725 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0340 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0725 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0342,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05956 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0725 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0394 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0725 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0342,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05957 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0725 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0725 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05958 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0342 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05959 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0725 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0725 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0342 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05960 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1615 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0725 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0725 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1615 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05961 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0598,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05962 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0296 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0598,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05963 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0305 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0598,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05964 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0341 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0598,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05965 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0395 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0598,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05966 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0726 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05967 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0598 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05968 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0598 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05969 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0598 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause05970 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0598 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05971 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0598 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05972 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1616 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0726 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1616 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05973 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1616 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1616 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0598 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05974 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0726 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1616 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0726 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1616 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0598 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause05975 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05976 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0297 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1110,
  ] at hbad
  tauto

end ErdosSzekeres

end
