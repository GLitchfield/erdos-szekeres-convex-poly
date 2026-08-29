module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment100

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 101. -/

theorem synchronizedFiveFanFin11Semantic_clause07265 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0887 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0415 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0887 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1476,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07266 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0887 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0417 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0887 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1476,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07267 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0887 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0488 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0488 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0887 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1476,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07268 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1330 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0887 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0887 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1330 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07269 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1330 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1330 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1476 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07270 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1774 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0887 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0887 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1774 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07271 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0888 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0414 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0888 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1732,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07272 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0888 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0415 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0888 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1732,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07273 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0888 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0418 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0888 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1732,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07274 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0888 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0888 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1732,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07275 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0888 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0888 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1732,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07276 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1331 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0888 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0888 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1331 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07277 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1775 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0888 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0888 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1775 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07278 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0889 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0416 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1860,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07279 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0889 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0417 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1860,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07280 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0889 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0418 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1860,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07281 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0889 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1860,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07282 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0889 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1860,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07283 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1332 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0889 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07284 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1860 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07285 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0889 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1860 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause07286 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0889 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1860 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause07287 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1776 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0889 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1776 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07288 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0889 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1776 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0889 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1776 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1860 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause07289 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0890 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0419 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0419 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0890 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1924,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07290 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0890 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0890 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1924,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07291 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1333 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0890 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0890 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1333 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07292 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0891 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0891 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0248,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07293 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0891 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0428 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0891 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0248,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07294 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0891 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0891 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0248,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07295 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0891 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0891 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0248,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07296 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1334 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0891 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0891 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1334 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07297 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1777 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0891 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0891 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1777 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07298 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0892 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0892 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0376,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07299 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0892 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0892 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0376,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07300 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0892 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0892 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0376,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07301 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0892 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0892 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0376,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07302 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0892 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0892 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0376,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07303 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0892 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0892 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0376,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07304 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1335 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0892 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0892 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1335 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07305 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1335 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0376 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07306 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1778 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0892 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0892 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1778 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07307 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0893 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0632,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07308 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0893 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0632,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07309 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0893 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0632,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07310 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0893 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0632,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07311 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0893 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0632,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07312 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0893 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0632,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07313 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1336 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0893 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07314 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0893 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0632 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause07315 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0893 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0632 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause07316 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0893 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0632 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause07317 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1779 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0893 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0893 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1779 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07318 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0894 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0894 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1144,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07319 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0894 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0894 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1144,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07320 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0894 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0894 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1144,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07321 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0894 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0894 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1144,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07322 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0894 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0894 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1144,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07323 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0894 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0894 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07324 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0894 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0894 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1780 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07325 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0895 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0461 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0461 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0895 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0440,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07326 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1338 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0895 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0895 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1338 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07327 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0896 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0424 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0896 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0696,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07328 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0896 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0896 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0696,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07329 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0896 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0896 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0696,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07330 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0896 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0896 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0696,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07331 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0896 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0896 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0696,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07332 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1339 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0896 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0896 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1339 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07333 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1781 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0896 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0896 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1781 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07334 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0897 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0424 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0897 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1208,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07335 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0897 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0897 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1208,
  ] at hbad
  tauto

end ErdosSzekeres

end
