module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment069

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 070. -/

theorem synchronizedFiveFanFin11Semantic_clause05041 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0606 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0398 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0606 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0661,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05042 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0606 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0606 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1058 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05043 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1499 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0606 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0606 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1499 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05044 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0607 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0211 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0607 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05045 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0607 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0607 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05046 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0607 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0226 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0226 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0607 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05047 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0607 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0261 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0261 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0607 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05048 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0607 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0399 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0607 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05049 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0607 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0607 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1059 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05050 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1500 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0607 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0607 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1500 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05051 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0608 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0212 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0608 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0789,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05052 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0608 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0213 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0608 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0789,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05053 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0608 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0227 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0608 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0789,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05054 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0608 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0262 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0608 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0789,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05055 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0608 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0400 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0608 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0789,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05056 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0608 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0608 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1060 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05057 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1060 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0789 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05058 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0608 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1060 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0608 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1060 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0789 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05059 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1501 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0608 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0608 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1501 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05060 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0609 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0212 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0609 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1301,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05061 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0609 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0609 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1301,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05062 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0609 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0228 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0609 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1301,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05063 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0609 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0263 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0609 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1301,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05064 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0609 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0401 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0609 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1301,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05065 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0609 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0609 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1061 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05066 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1061 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1301 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05067 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1502 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0609 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0609 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1502 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05068 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0610 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0213 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05069 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0610 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05070 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0610 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0229 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05071 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0610 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0264 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05072 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0610 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0402 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05073 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0610 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1062 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05074 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1062 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1557 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05075 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0610 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1062 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1062 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1557 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05076 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0610 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1062 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1062 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1557 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause05077 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0610 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1062 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1062 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1557 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05078 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1503 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0610 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0610 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1503 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05079 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0611 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0215 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0611 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0229,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05080 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0611 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0611 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0229,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05081 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0611 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0220 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0611 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0229,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05082 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0611 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0265 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0611 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0229,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05083 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0611 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0611 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0229,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05084 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1063 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0611 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0611 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1063 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05085 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1504 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0611 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0611 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1504 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05086 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0612 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0215 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0357,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05087 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0612 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0217 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0357,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05088 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0612 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0221 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0357,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05089 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0612 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0266 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0357,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05090 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0612 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0357,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05091 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0612 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1064 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05092 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1064 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0357 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05093 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0612 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1064 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1064 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0357 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05094 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0612 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1064 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1064 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0357 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause05095 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1505 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0612 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1505 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05096 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0612 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1505 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0612 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1505 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0357 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause05097 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0215 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0613,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05098 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0218 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0613,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05099 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0222 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0613,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05100 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0613,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05101 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0405 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0613,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05102 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0613 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1065 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05103 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1065 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0613 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05104 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1065 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1065 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0613 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11Semantic_clause05105 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1065 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1065 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0613 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05106 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1506 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0613 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1506 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05107 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1506 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1506 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0613 chi).mpr
  have hright0 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05108 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1506 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1506 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0613 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05109 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1506 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1506 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0613 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause05110 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0613 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1506 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0613 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1506 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0613 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause05111 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0614 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0215 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1125,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05112 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0614 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0219 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1125,
  ] at hbad
  tauto

end ErdosSzekeres

end
