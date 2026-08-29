module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Common alternate-depth-two clauses, segment 015. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09162 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0537 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0999 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0537 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0999 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0587 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09458 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1009 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask0307 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12097 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0635 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0635 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1097 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12228 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0639 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1101 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0639 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1101 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0569 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14957 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0730 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1192 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0730 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1192 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0566 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17048 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1262 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1262 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask1138 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17887 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1290 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0828 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0828 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1290 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18851 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0860 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0860 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1322 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0844 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21166 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0937 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1399 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0937 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1399 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0496 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21818 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0168 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0169 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0171 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0187 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0189 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0193 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0215 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0217 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0221 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0267 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0299 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0301 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0305 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0351 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0407 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0168 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0169 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0171 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0187 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0189 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0193 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0215 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0217 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0221 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0267 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0299 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0301 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0305 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0351 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0407 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 5, 6, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0358 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 5, 6, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0357 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0355 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0327 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 5, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0295 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 5, 6} := by
    apply (fin11AltDepth2_strongSet_iff_mask0103 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 0 =
          {1, 2, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 1 =
          {0, 2, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 2 =
          {0, 1, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21835 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0170 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0172 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0173 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0197 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0198 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0201 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0225 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0226 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0229 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0284 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0309 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0310 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0313 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0368 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0424 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0170 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0172 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0173 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0197 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0198 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0201 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0225 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0226 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0229 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0284 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0309 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0310 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0313 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0368 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0424 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 7, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1670 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 7, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1669 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 7, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1667 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1543 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 7, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1159 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 7, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0647 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {0, 1, 2, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23625 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1060 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1075 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1306 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1045 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1046 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1060 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1075 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1110 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1306 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 3, 4, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0797
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23949 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0091 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1338 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0091 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h14
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
  refine ⟨{0, 2, 4, 5, 9, 10}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24007 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1071 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1344 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1070 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1071 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1077 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1093 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1148 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1344 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 6, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1621
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24841 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1169 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1172 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1196 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1231 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1301 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1169 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1172 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1181 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1196 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1231 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1301 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 4, 6, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0606
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26537 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1351 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1356 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1360 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1415 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1349 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1351 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1353 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1356 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1360 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1415 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 5, 6, 7, 8, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1508
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 5, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26545 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1350 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1351 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1354 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1357 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1416 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1350 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1351 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1354 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1357 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1361 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1416 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 5, 6, 7, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1764
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 5, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23594 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0057 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1506 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1507 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1519 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1534 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1569 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1765 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0057 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1506 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1507 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1519 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1534 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1569 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1765 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 3, 4, 7, 8}, 1, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0413
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24508 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1585 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1586 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1588 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1591 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1856 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1585 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1586 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1588 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1591 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1625 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1856 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 6, 7, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0969
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 3, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 6, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24602 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1596 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1598 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1603 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1609 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1619 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1865 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1596 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1598 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1603 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1609 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1619 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1865 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 4, 5, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1393
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24610 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1597 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1598 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1604 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1610 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1620 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1866 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1597 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1598 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1604 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1610 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1620 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1866 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 4, 5, 6, 9, 10}, 7, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1649
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25568 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1691 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1695 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1711 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1731 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1836 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1691 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1692 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1695 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1711 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1731 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1836 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 4, 6, 7, 8}, 5, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0474
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26506 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1804 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1805 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1806 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1810 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1824 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1874 chi) := by
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
  unfold SynchronizedFiveFanFin11OriginalAtom1804 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1805 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1806 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1810 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1824 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1874 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 4, 6, 8, 9, 10}, 1, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1876
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01084 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0091 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0091 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01877 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02336 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02497 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0150 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03099 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0091 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0091 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04369 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04973 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05235 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05936 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06242 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06751 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0152 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06989 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07780 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09932 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0563 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0191 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0191 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0563 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1123,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11014 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0599 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0249 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0249 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0599 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1293,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12121 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0636 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0230 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0230 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0636 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0121,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13291 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0675 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0252 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0252 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0675 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0433,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14435 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0713 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0377 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0713 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15605 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0752 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0416 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0416 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0752 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0454,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16804 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0792 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0365 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0365 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0792 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1610,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17973 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0831 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0368 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0831 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1922,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19111 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0869 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0391 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0391 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0869 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0628,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20254 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0907 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0446 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0907 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0696,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21482 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0473 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0473 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0948 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1488,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01365 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01823 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0241 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0241 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03250 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03695 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0319 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0319 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04151 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0338 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0338 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04409 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04689 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0361 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0361 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05100 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0378 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06736 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07186 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0465 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07306 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0470 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07528 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0479 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07881 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0494 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0494 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08004 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0498 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0498 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1422 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0079 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09799 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1482 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0558 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0558 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1482 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11100 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0601 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1525 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0601 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1525 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0117 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14181 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0704 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1628 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0704 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1628 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1857 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15559 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1674 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0750 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0750 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1674 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18740 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1780 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1780 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask1580 chi).mpr
  have hright0 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18930 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0862 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1786 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0862 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1786 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1612 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21259 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1864 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0940 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0940 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1864 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
