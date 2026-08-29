module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Common alternate-depth-two clauses, segment 167. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08408 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0974 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0974 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask0551 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10567 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0584 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0584 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1046 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11292 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0608 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1070 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0608 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1070 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0597 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13634 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0686 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0686 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1148 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16148 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1232 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0139 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1232 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask1114 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16447 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1242 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0780 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0780 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1242 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18374 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0844 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1306 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0844 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1306 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0796 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19818 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0892 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1354 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0892 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1354 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1636 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22204 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0396 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0397 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0398 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0400 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0401 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0403 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0416 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0417 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0419 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0422 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0471 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0472 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0474 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0477 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0491 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0396 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0397 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0398 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0400 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0401 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0403 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0416 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0417 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0419 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0422 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0471 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0472 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0474 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0477 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0491 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 6, 7, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0976 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 6, 7, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0964 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 7, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0916 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 6, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0852 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 6, 7, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0724 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 6, 7, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0468 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 6, 7, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 6, 7, 8, 9} : Finset (Fin 11))) :
      y ∈ ({2, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 2 =
          {4, 6, 7, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 4 =
          {2, 6, 7, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 6 =
          {2, 4, 7, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 7 =
          {2, 4, 6, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 8 =
          {2, 4, 6, 7, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 9 =
          {2, 4, 6, 7, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22210 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0406 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0407 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0409 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0410 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0412 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0414 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0416 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0418 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0420 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0423 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0481 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0483 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0485 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0488 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0492 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0406 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0407 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0409 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0410 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0412 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0414 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0416 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0418 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0420 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0423 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0481 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0483 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0485 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0488 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0492 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 6, 7, 8, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1504 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 6, 7, 8, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1476 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 5, 7, 8, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1444 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 5, 6, 8, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1380 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 5, 6, 7, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1252 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 5, 6, 7, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0484 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 5, 6, 7, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 5, 6, 7, 8, 10} : Finset (Fin 11))) :
      y ∈ ({2, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 2 =
          {5, 6, 7, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 5 =
          {2, 6, 7, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 6 =
          {2, 5, 7, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 7 =
          {2, 5, 6, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 8 =
          {2, 5, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 10 =
          {2, 5, 6, 7, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22797 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0983 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0985 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1223 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0983 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0984 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom0985 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1041 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1097 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1223 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 8, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1799
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22973 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0992 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0995 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1115 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1241 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0992 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0995 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom0999 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1024 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1115 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1241 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 5, 6, 9}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0619
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 5, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23447 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1288 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1029 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1030 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1031 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1041 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1162 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1288 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 8, 9, 10}, 4, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1827
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24161 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1091 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1163 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1359 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1088 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1089 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1091 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1094 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1163 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1359 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 6, 7, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0965
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 6, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26149 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1299 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1302 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1305 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1321 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1376 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1299 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1302 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1305 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1321 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1341 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1376 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 3, 4, 6, 7, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
      | exact right_of_not_left _ h4
      | exact h5
      | exact h6
      | exact h7
      | exact right_of_not_left _ h8
      | exact h9
      | exact h10
      | exact right_of_not_left _ h11
      | exact h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1244
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 3, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26215 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1306 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1307 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1308 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1328 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1383 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1306 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1307 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1308 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1328 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1348 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1383 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 3, 4, 8, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1820
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 3, 4, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22476 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1430 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1435 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1471 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1527 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1653 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1427 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1430 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1435 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1471 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1527 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1653 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 8}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0311
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23898 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1526 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1527 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1534 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1544 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1599 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1795 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1526 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1527 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1534 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1544 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1599 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1795 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 5, 7, 8}, 6, by decide, by decide, Or.inr ?_⟩
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
      | exact h3
      | exact h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact h7
      | exact h8
      | exact right_of_not_left _ h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask0437
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24166 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1550 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1552 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1554 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1557 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1822 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1550 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1552 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1554 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1557 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1626 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1822 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 6, 7, 8, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1477
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 6, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24294 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1563 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1564 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1574 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1584 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1604 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1835 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1563 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1564 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1574 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1584 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1604 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1835 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 4, 5, 9, 10}, 1, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1593
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24338 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1566 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1567 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1572 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1588 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1608 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1839 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1566 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1567 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1572 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1588 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1608 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1839 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 4, 6, 8, 9}, 5, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0857
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 3, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26442 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1795 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1796 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1798 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1807 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1817 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1867 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1795 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1796 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1798 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1807 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1817 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1867 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 4, 5, 7, 8, 9}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0948
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 4, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00915 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0084 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01372 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01976 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02113 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02933 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0084 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03506 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04731 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04827 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05552 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05761 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0146 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06127 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06725 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07611 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08581 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0518 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0170 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0170 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0518 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0391,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09632 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0553 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0186 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0186 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0553 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10654 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0587 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0237 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0237 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0587 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11821 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0626 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0220 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0220 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0626 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0453,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13021 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0666 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0243 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0243 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0666 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1609,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14163 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0704 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0281 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0281 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0704 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1857,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15305 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0742 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0406 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0742 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0230,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16473 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0781 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0329 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0329 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0781 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0426,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17643 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0820 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0357 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0357 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0820 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0866,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18871 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0861 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0382 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0861 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1356,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19356 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0877 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0396 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0397 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0400 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0416 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0396 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0397 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0400 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0416 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0471 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0877 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0468,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19954 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0897 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0422 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0897 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0964,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21212 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0939 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0464 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0939 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1264,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01077 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0210 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01439 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0225 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0225 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02855 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0284 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0284 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03060 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0293 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03705 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0320 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0320 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03839 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0057 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0325 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0057 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0325 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03977 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0057 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0331 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0057 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0331 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04821 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0366 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06336 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0429 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06852 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0451 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06972 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0456 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07041 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0459 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07072 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08239 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1430 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0506 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0506 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1430 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13223 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0672 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1596 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0672 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1596 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0369 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14029 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1623 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0699 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0699 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1623 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16640 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1710 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1710 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask1578 chi).mpr
  have hright0 : chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18562 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0850 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1774 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0850 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1774 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1132 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19759 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1814 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0890 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0890 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1814 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20850 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0926 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1850 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0926 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1850 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1384 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

end ErdosSzekeres

end
