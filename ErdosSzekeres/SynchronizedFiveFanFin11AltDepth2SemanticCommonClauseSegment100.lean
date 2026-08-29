module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Common alternate-depth-two clauses, segment 100. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08169 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0504 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0966 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0504 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0966 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0087 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11587 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1080 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0618 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0618 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1080 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11595 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0618 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1080 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0618 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1080 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0613 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14266 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0707 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0707 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1169 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0094 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14588 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1180 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1180 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask0334 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17347 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1272 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0810 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0810 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1272 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18522 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0849 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1311 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0849 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1311 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20175 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0904 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1366 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0904 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1366 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0632 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20888 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1390 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1390 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask0936 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22033 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0286 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0287 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0288 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0293 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0294 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0299 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0314 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0315 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0320 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0335 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0370 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0371 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0376 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0391 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0286 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0287 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0288 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0293 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0294 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0299 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0314 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0315 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0320 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0335 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0370 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0371 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0376 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0391 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0426 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 6} := by
    apply (fin11AltDepth2_strongSet_iff_mask0124 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 5, 6} := by
    apply (fin11AltDepth2_strongSet_iff_mask0122 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 5, 6} := by
    apply (fin11AltDepth2_strongSet_iff_mask0118 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 5, 6} := by
    apply (fin11AltDepth2_strongSet_iff_mask0110 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 6} := by
    apply (fin11AltDepth2_strongSet_iff_mask0094 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 5} := by
    apply (fin11AltDepth2_strongSet_iff_mask0062 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 6}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 5, 6} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 5, 6} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 5, 6} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 5, 6} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 4, 6} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22063 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0288 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0291 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0292 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0306 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0307 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0313 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0327 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0328 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0334 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0365 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0383 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0384 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0390 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0421 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0288 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0291 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0292 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0306 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0307 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0313 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0327 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0328 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0334 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0365 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0383 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0384 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0390 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0421 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0456 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 6, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1612 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 6, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1610 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1606 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1550 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 6, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1102 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 6, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0590 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23281 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1015 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1018 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1271 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1012 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1015 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1018 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1034 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1145 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1271 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 7, 10}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1235
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24461 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1115 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1158 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1389 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1115 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1116 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1122 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1128 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1158 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1389 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 5, 6, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1641
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 3, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24835 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1169 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1172 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1196 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1231 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1301 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1169 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1172 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1181 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1196 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1231 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1301 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 4, 6, 9}, 5, by decide, by decide, Or.inl ?_⟩
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25147 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0091 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1189 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1193 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1207 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1262 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1332 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0091 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1189 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1193 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1197 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1207 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1262 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1332 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 5, 6, 10}, 7, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1142
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 5, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25311 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1202 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1203 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1223 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1278 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1348 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0091 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1201 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1202 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1203 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1223 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1278 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1348 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 8, 9, 10}, 7, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1814
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25319 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1204 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1205 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1208 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1214 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1279 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1349 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1204 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1205 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1208 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1214 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1279 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1349 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 7, 8}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0486
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25329 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1204 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1206 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1209 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1215 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1280 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1350 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1204 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1206 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1209 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1215 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1280 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1350 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 7, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0742
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22642 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1487 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1543 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1669 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1433 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1437 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1441 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1487 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1543 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1669 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 6, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1127
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23882 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1525 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1528 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1532 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1542 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1597 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1793 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1525 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1528 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1532 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1542 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1597 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1793 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 5, 6, 9}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0629
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25368 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1668 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1669 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1675 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1681 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1746 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1816 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1668 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1669 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1675 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1681 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1746 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1816 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1638
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25742 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1707 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1718 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1748 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1853 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1705 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1707 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1709 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1718 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1748 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1853 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1450
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26260 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1772 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1773 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1778 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1784 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1814 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1849 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1772 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1773 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1778 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1784 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1814 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1849 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 3, 5, 6, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0876
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00222 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0055 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00464 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00530 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0068 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02070 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03463 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0106 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03507 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0108 chi) := by
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03917 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0057 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0057 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04064 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04177 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05790 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06582 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07225 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0152 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08912 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0529 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0180 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0180 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0529 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1051,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09781 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0558 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0184 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0184 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0558 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10953 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0597 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0226 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0226 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0597 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1165,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12005 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0632 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0422 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0632 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0901,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13175 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0671 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0461 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0461 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0671 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0241,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14344 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0710 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0318 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0710 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0542,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15514 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0357 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0357 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0749 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0806,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16683 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0788 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0330 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0330 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0788 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0714,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17852 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0827 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0361 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0361 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0827 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0962,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19025 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0866 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0460 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0866 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1804,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20163 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0904 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0433 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0904 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0632,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21331 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0943 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0465 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0943 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0944,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00191 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0173 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00096 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0169 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00201 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0174 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00202 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0174 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01785 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0240 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01985 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0248 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0248 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02157 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0255 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0255 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02543 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0271 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03778 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0323 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0323 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04895 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0369 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0369 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04991 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0373 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0373 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05676 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0402 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0091 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0402 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05626 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0400 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0091 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0400 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07728 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0487 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0487 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09259 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0540 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0540 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1464 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10733 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0589 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1513 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0589 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1513 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0557 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13220 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1596 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1596 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask0369 chi).mpr
  have hright0 : chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13582 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0684 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1608 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0684 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1608 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0849 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15019 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1656 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0732 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0732 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1656 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18720 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0855 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1779 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0855 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1779 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1324 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20839 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1850 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0926 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0926 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1850 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
