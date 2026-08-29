module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Common alternate-depth-two clauses, segment 186. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08418 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0512 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0974 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0512 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0974 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0551 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11980 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0631 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1093 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0631 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1093 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1605 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14507 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0715 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0715 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1177 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0558 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14797 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1187 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0725 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0725 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1187 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18669 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0854 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1316 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0854 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1316 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0812 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20416 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0912 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0912 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1374 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0472 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20497 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1377 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0915 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0915 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1377 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22240 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0465 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0466 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0467 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0468 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0469 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0470 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0477 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0478 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0479 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0480 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0487 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0488 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0489 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0490 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0495 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0465 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0466 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0467 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0468 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0469 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0470 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0477 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0478 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0479 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0480 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0487 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0488 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0489 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0490 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0495 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 7, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1952 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {4, 7, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1936 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {4, 5, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1840 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {4, 5, 7, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1712 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {4, 5, 7, 8, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1456 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {4, 5, 7, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0944 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{4, 5, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({4, 5, 7, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({4, 5, 7, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({4, 5, 7, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({4, 5, 7, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {5, 7, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 7, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {4, 7, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 7, 8, 9, 10} : Finset (Fin 11)).erase 7 =
          {4, 5, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 7, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {4, 5, 7, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 7, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {4, 5, 7, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 7, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {4, 5, 7, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22685 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0973 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1212 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0973 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0975 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom0984 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1030 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1086 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1212 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 8, 10}, 4, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1319
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 5, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23043 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0995 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1248 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0995 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0996 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1006 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1031 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1122 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1248 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 5, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1579
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23291 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1014 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1146 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1272 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1013 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1014 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1019 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1035 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1146 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1272 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0851
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24227 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1105 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1115 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1366 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1098 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1101 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1105 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1115 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1135 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1366 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 4, 5, 6, 9}, 7, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0633
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 5, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24521 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1125 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1127 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1395 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1123 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1125 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1127 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1130 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1164 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1395 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 6, 7, 8, 10}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1481
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 3, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 6, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 6, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26641 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1366 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1367 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1373 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1379 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1404 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1366 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1367 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1373 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1379 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1389 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1404 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1656
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22870 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1449 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1460 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1475 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1566 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1692 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1449 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1451 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1460 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1475 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1566 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1692 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 8}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0347
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23064 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1459 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1461 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1495 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1586 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1712 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1459 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1461 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1464 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1495 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1586 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1712 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 6, 7, 9}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0715
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23750 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1513 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1514 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1524 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1549 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1584 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1780 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1513 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1514 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1524 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1549 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1584 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1780 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 3, 5, 9, 10}, 7, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1581
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25556 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1690 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1710 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1730 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1835 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1689 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1690 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1700 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1710 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1730 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1835 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 4, 5, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1594
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25654 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1698 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1720 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1740 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1845 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1698 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1699 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1700 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1720 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1740 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1845 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 4, 8, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1818
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 4, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26114 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1759 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1760 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1770 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1780 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1800 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1835 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1759 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1760 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1770 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1780 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1800 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1835 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 3, 4, 5, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1596
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 3, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26168 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1762 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1764 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1769 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1785 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1805 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1840 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1762 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1764 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1769 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1785 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1805 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1840 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 3, 4, 6, 8, 10}, 5, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1372
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 3, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00436 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00943 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0085 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01034 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01657 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0115 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02331 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04014 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04180 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04400 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04543 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04682 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06077 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06965 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07777 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08854 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0527 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0233 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0233 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0527 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0283,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10082 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0568 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0191 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0191 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0568 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1315,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11164 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0254 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0254 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0604 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0565,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12331 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0643 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0231 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0643 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0601,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12816 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0659 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0238 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0240 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0249 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0274 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0449 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0238 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0240 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0249 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0274 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0449 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0659 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1321,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13501 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0682 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0256 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0256 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0682 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0721,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14671 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0721 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0289 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0289 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0721 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0398,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15845 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0760 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0424 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0424 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0760 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1670,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16984 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0798 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0351 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0351 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0798 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0370,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18154 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0837 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0396 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0837 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0220,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19411 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0879 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0396 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0879 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1236,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20524 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0916 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0455 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0916 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1368,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21662 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0483 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0483 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0954 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1760,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00586 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00688 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0194 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0194 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01799 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0240 chi) := by
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01713 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0237 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0237 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02469 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0268 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0268 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02772 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0281 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0281 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03239 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03681 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0319 chi) := by
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04236 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0342 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05584 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0398 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06136 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06178 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06274 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10888 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0594 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1518 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0594 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1518 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1101 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12409 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1569 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0645 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0645 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1569 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12860 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1584 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1584 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask1577 chi).mpr
  have hright0 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13645 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0686 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1610 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0686 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1610 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18169 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1761 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0837 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0837 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1761 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18470 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1771 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0146 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1771 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask0236 chi).mpr
  have hright0 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 7, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 7, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18747 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0856 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1780 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0856 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1780 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1580 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

end ErdosSzekeres

end
