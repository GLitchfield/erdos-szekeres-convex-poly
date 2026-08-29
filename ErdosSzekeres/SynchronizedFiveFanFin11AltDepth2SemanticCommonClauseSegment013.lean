module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Common alternate-depth-two clauses, segment 013. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08298 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0508 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0970 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0508 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0970 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1047 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09368 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1006 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1006 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask1547 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09967 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0564 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0564 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1026 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11174 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1066 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0604 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1066 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0565 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13601 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0685 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0685 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1147 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1361 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15757 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1219 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0757 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0757 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1219 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16898 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1257 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0057 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0057 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1257 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask1674 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18191 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0838 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0838 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1300 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0348 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19779 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0891 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1353 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0891 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1353 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1380 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21517 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0949 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0949 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1411 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21814 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0167 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0171 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0172 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0184 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0185 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0199 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0212 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0213 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0227 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0263 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0296 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0297 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0311 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0347 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0167 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0171 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0172 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0184 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0185 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0199 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0212 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0213 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0227 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0263 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0296 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0297 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0311 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0347 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0403 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0790 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0789 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0787 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0775 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0535 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0279 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 4, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21832 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0169 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0172 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0173 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0194 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0195 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0201 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0222 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0223 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0229 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0281 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0306 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0307 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0313 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0365 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0169 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0172 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0173 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0194 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0195 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0201 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0222 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0223 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0229 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0281 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0306 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0307 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0313 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0365 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0421 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 6, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1606 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 6, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1605 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1603 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1543 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 6, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1095 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 6, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0583 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23595 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1057 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1072 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1303 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1044 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1045 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1057 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1072 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1107 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1303 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 3, 4, 7, 8}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact h5
      | exact h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask0413
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23945 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1338 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1066 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1067 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1077 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1087 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1142 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1338 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 5, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1589
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23977 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1068 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1071 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1090 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1341 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1068 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1071 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1074 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1090 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1145 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1341 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 6, 7, 10}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1237
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24801 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1168 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1172 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1192 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1227 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1297 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1168 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1172 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1177 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1192 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1227 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1297 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 4, 5, 9}, 10, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask0574
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26505 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1344 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1362 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1412 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1342 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1343 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1344 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1348 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1362 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1412 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 4, 6, 8, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1876
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26507 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1344 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1362 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1412 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1342 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1343 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1344 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1348 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1362 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1412 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 4, 6, 8, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1876
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23568 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1505 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1507 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1516 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1531 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1566 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1762 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0091 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1505 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1507 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1516 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1531 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1566 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1762 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 3, 4, 6, 8}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact h11
      | exact right_of_not_left _ h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask0349
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24438 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1576 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1577 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1582 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1588 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1618 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1849 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1576 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1577 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1582 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1588 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1618 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1849 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 5, 6, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask0873
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24540 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1588 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1589 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1590 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1594 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1628 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1859 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1588 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1589 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1590 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1594 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1628 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1859 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 6, 8, 9, 10}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1865
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 3, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24582 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1595 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1598 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1601 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1607 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1617 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1863 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1595 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1598 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1601 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1607 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1617 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1863 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 4, 5, 6, 7, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact h11
      | exact right_of_not_left _ h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1265
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25248 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1657 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1658 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1679 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1734 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1804 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1657 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1658 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1663 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1679 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1734 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1804 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 8, 9}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact h2
      | exact h3
      | exact h4
      | exact right_of_not_left _ h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask0854
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26466 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1798 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1799 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1800 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1810 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1820 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1870 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1798 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1799 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1800 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1810 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1820 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1870 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 4, 5, 8, 9, 10}, 1, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1844
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01062 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0090 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01875 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02288 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0141 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02449 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03077 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0090 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04321 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0142 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04971 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05141 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05888 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06145 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06679 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06987 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07758 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08554 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0517 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0223 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0223 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0517 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1095,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09392 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0545 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0182 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0545 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0115,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10534 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0583 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0233 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0233 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0583 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0285,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11761 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0624 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0217 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0217 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0624 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1317,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12871 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0661 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0241 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0241 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0661 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0457,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14043 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0700 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0275 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0275 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0700 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1825,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15245 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0740 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0404 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0740 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16352 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0777 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0321 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0321 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0777 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17612 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0819 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0353 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0353 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0819 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1250,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18721 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0856 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0379 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0379 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0856 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1580,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19834 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0893 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0422 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0893 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0932,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21002 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0932 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0452 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0932 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0968,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21426 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0946 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0468 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0469 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0470 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0480 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0468 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0469 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0470 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0480 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0490 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0946 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1840,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01356 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0222 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0222 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01776 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0239 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03233 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03552 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0313 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0313 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04128 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0337 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04402 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0349 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04593 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0357 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0357 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05085 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0377 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06719 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07145 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0463 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0463 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07289 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0469 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0469 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07511 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0478 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07833 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0492 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0492 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13399 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1602 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0678 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0678 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1602 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13617 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0685 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1609 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0685 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1609 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1361 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18650 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1777 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0152 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1777 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask1196 chi).mpr
  have hright0 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 7, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 7, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 7, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18712 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0855 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1779 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0855 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1779 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1324 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19249 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1797 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0873 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0873 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1797 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
