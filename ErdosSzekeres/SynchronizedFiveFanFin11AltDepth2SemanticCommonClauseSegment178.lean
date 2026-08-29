module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Common alternate-depth-two clauses, segment 178. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08264 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0507 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0969 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0507 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0969 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0535 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11799 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0625 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1087 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0625 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1087 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1573 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14356 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0710 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0710 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1172 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0542 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14497 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0715 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0715 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1177 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18527 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0849 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1311 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0849 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1311 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20257 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1369 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0907 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0907 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1369 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20349 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0910 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0910 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1372 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1336 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22229 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0435 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0436 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0437 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0438 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0439 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0440 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0457 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0458 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0459 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0460 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0477 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0478 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0479 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0480 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0495 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0435 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0436 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0437 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0438 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0439 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0440 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0457 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0458 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0459 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0460 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0477 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0478 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0479 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0480 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0495 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 7, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1936 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 7, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1928 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 4, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1816 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 4, 7, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1688 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 4, 7, 8, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1432 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 4, 7, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0920 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 4, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 4, 7, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 4, 7, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({3, 4, 7, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 4, 7, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {4, 7, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 7, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {3, 7, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 7, 8, 9, 10} : Finset (Fin 11)).erase 7 =
          {3, 4, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 7, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {3, 4, 7, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 7, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {3, 4, 7, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 7, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {3, 4, 7, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22493 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0965 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0970 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1011 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1193 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0965 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0970 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom0975 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1011 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1067 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1193 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1079
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22885 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0987 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0991 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1000 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1015 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1232 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0987 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0991 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1000 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1015 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1106 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1232 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1115
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23001 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0993 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0994 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1243 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0993 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0994 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1001 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1026 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1117 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1243 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 5, 7, 8}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0427
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 5, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23963 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1068 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1073 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1340 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1068 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1070 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1073 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1089 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1144 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1340 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 6, 7, 9}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0725
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24381 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1111 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1150 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1381 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1107 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1109 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1111 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1130 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1150 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1381 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 4, 7, 8, 10}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1433
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 3, 4, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26499 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1340 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1344 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1347 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1411 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1340 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1341 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1344 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1347 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1361 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1411 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 4, 6, 7, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1748
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22480 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1430 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1435 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1471 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1527 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1653 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h14
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
  refine ⟨{0, 1, 2, 4, 5, 8}, 9, by decide, by decide, Or.inr ?_⟩
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22904 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1479 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1570 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1696 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0091 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1450 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1452 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1464 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1479 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1570 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1696 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 7, 9}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0667
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23586 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1505 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1509 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1518 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1533 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1568 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1764 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1505 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1509 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1518 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1533 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1568 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1764 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 3, 4, 6, 10}, 5, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1117
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25064 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1643 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1644 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1650 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1681 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1716 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1786 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1643 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1644 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1650 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1681 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1716 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1786 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 6, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1614
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25362 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1667 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1669 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1674 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1680 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1745 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1815 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1667 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1669 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1674 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1680 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1745 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1815 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1382
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25760 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1710 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1720 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1750 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1855 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1708 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1709 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1710 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1720 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1750 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1855 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 8, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1834
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25804 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1717 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1718 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1719 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1720 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1755 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1860 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1717 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1718 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1719 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1720 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1755 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1860 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 7, 8, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1930
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 7, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 7, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 7, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00366 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00799 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00889 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01273 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02214 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03894 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04160 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04108 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04423 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0146 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04514 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0150 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06005 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06893 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07657 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08821 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0526 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0174 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0526 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0155,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09964 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0564 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0270 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0270 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0564 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0419,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11131 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0603 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0209 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0603 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0309,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11796 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0625 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0218 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0219 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0229 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0275 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0415 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0218 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0219 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0229 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0275 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0415 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0625 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1573,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12273 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0641 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0241 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0241 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0641 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0217,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13533 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0683 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0262 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0262 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0683 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1233,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14612 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0719 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0291 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0291 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0719 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0590,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15782 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0758 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0309 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0309 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0758 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0902,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16951 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0797 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0335 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0335 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0797 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0242,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18241 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0840 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0371 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0840 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1116,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19263 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0874 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0403 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0874 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0820,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20431 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0913 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0431 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0913 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0728,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21634 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0953 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0488 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0488 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0953 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1504,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00525 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0187 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0187 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00599 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0190 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0190 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01257 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0218 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0218 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01464 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0226 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0226 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02421 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0266 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0266 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02700 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0278 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0278 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02865 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0285 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0285 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03143 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0296 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0296 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04188 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0340 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0340 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05495 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0394 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0394 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05999 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0415 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0415 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06106 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0420 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0420 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06084 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0419 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0419 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10737 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0589 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1513 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0589 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1513 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0557 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11630 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1543 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1543 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask1125 chi).mpr
  have hright0 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12169 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1561 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0637 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0637 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1561 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13586 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0684 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1608 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0684 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1608 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0849 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h5)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17180 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1728 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1728 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask0818 chi).mpr
  have hright0 : chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17959 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1754 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0830 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0830 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1754 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18685 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0854 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1778 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0854 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1778 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0812 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

end ErdosSzekeres

end
