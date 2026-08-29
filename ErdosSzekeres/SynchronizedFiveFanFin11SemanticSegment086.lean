module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment085

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 086. -/

theorem synchronizedFiveFanFin11Semantic_clause06193 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0752 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0752 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06194 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0753 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0313 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0122,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06195 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0753 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0122,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06196 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0753 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0319 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0122,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06197 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0753 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0334 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0122,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06198 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0753 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0122,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06199 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0753 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0122,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06200 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1202 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0753 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1202 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06201 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1202 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0122 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06202 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0753 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1202 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1202 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0122 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06203 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0753 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1202 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1202 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0122 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause06204 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1643 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0753 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0753 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1643 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06205 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0754 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0313 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0754 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0186,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06206 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0754 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0315 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0754 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0186,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06207 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0754 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0320 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0754 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0186,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06208 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0754 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0335 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0754 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0186,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06209 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0754 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0424 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0754 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0186,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06210 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1203 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0754 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0754 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1203 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06211 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1644 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0754 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0754 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1644 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06212 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0755 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0313 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0755 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0314,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06213 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0755 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0316 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0755 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0314,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06214 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0755 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0321 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0755 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0314,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06215 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0755 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0755 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0314,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06216 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0755 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0755 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0314,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06217 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1204 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0755 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0755 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1204 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06218 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1645 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0755 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0755 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1645 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06219 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0756 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0313 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0756 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0570,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06220 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0756 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0317 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0756 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0570,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06221 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0756 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0756 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0570,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06222 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0756 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0756 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0570,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06223 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0756 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0756 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0570,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06224 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0756 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0756 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0570,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06225 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1205 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0756 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0756 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1205 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06226 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1646 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0756 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0756 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1646 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06227 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1646 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1646 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0570 chi).mpr
  have hright0 : chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06228 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0757 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0313 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0757 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1082,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06229 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0757 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0757 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1082,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06230 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0757 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0323 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0757 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1082,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06231 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0757 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0338 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0757 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1082,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06232 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0757 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0757 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1082,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06233 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1206 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0757 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0757 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1206 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06234 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1647 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0757 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0757 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1647 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06235 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0758 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0758 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0218,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06236 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0758 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0315 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0758 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0218,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06237 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0758 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0758 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0218,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06238 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0758 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0339 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0758 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0218,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06239 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0758 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0428 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0758 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0218,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06240 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1207 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0758 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0758 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1207 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06241 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1648 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0758 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0758 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1648 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06242 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0759 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0759 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0346,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06243 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0759 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0316 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0759 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0346,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06244 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0759 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0325 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0759 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0346,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06245 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0759 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0340 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0759 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0346,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06246 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0759 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0759 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0346,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06247 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1208 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0759 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0759 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1208 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06248 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1208 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0346 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06249 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0759 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1208 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0759 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1208 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0346 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06250 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1649 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0759 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0759 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1649 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06251 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0602,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06252 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0317 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0602,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06253 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0326 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0602,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06254 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0341 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0602,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06255 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0602,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06256 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1209 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0760 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06257 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0602 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06258 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0602 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06259 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0602 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause06260 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0602 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06261 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1650 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0760 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1650 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06262 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0760 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1650 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0760 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1650 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0602 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06263 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0761 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0761 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1114,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06264 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0761 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0761 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1114,
  ] at hbad
  tauto

end ErdosSzekeres

end
