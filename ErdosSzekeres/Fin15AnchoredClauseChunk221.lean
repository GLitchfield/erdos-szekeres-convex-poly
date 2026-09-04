module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 221. -/

theorem fin15Anchored_clause28288 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1837 Fin15AnchoredAtom1839 Fin15AnchoredAtom1878
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2198 Fin15AnchoredAtom2913 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 10, 12}, {0, 2, 4, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 2, 10, 12}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28289 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1837 Fin15AnchoredAtom1840 Fin15AnchoredAtom1879
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2199 Fin15AnchoredAtom2914 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 10, 13}, {0, 2, 4, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28290 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1837 Fin15AnchoredAtom1841 Fin15AnchoredAtom1880
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2200 Fin15AnchoredAtom2915 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 10, 14}, {0, 2, 4, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28291 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1838 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1881 chi ∧
      Fin15AnchoredAtom1981 chi ∧
      Fin15AnchoredAtom2201 chi ∧
      Fin15AnchoredAtom2916 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1838 Fin15AnchoredAtom1839 Fin15AnchoredAtom1881
    Fin15AnchoredAtom1981 Fin15AnchoredAtom2201 Fin15AnchoredAtom2916 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 11, 12}, {0, 2, 4, 11, 12}, {0, 1, 4, 11, 12}, {0, 1, 2, 11, 12}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28292 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1839 Fin15AnchoredAtom1840 Fin15AnchoredAtom1884
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2204 Fin15AnchoredAtom2919 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 12, 13}, {0, 2, 4, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 2, 12, 13}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28293 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1839 Fin15AnchoredAtom1841 Fin15AnchoredAtom1885
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2205 Fin15AnchoredAtom2920 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 12, 14}, {0, 2, 4, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28294 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1840 Fin15AnchoredAtom1841 Fin15AnchoredAtom1886
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2206 Fin15AnchoredAtom2921 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 13, 14}, {0, 2, 4, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 2, 13, 14}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28295 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2922 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1851
    Fin15AnchoredAtom1987 Fin15AnchoredAtom2207 Fin15AnchoredAtom2922 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 6, 7}, {0, 2, 5, 6, 7}, {0, 1, 5, 6, 7}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28296 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom1852 chi ∧
      Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom2208 chi ∧
      Fin15AnchoredAtom2923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1844 Fin15AnchoredAtom1852
    Fin15AnchoredAtom1988 Fin15AnchoredAtom2208 Fin15AnchoredAtom2923 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 6, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 6, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 6, 8}, {0, 2, 5, 6, 8}, {0, 1, 5, 6, 8}, {0, 1, 2, 6, 8}, {0, 1, 2, 5, 8}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28297 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1853
    Fin15AnchoredAtom1989 Fin15AnchoredAtom2209 Fin15AnchoredAtom2924 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 6, 9}, {0, 2, 5, 6, 9}, {0, 1, 5, 6, 9}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28298 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1854
    Fin15AnchoredAtom1990 Fin15AnchoredAtom2210 Fin15AnchoredAtom2925 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 6, 10}, {0, 2, 5, 6, 10}, {0, 1, 5, 6, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28299 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1847 chi ∧
      Fin15AnchoredAtom1855 chi ∧
      Fin15AnchoredAtom1991 chi ∧
      Fin15AnchoredAtom2211 chi ∧
      Fin15AnchoredAtom2926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1847 Fin15AnchoredAtom1855
    Fin15AnchoredAtom1991 Fin15AnchoredAtom2211 Fin15AnchoredAtom2926 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 6, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 6, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 6, 11}, {0, 2, 5, 6, 11}, {0, 1, 5, 6, 11}, {0, 1, 2, 6, 11}, {0, 1, 2, 5, 11}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28300 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1848 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1992 Fin15AnchoredAtom2212 Fin15AnchoredAtom2927 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 6, 12}, {0, 2, 5, 6, 12}, {0, 1, 5, 6, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28301 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1849 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1993 Fin15AnchoredAtom2213 Fin15AnchoredAtom2928 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 6, 13}, {0, 2, 5, 6, 13}, {0, 1, 5, 6, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28302 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1850 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1994 Fin15AnchoredAtom2214 Fin15AnchoredAtom2929 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 6, 14}, {0, 2, 5, 6, 14}, {0, 1, 5, 6, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28303 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom1859 chi ∧
      Fin15AnchoredAtom1995 chi ∧
      Fin15AnchoredAtom2215 chi ∧
      Fin15AnchoredAtom2930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1844 Fin15AnchoredAtom1859
    Fin15AnchoredAtom1995 Fin15AnchoredAtom2215 Fin15AnchoredAtom2930 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 7, 8}, {0, 2, 5, 7, 8}, {0, 1, 5, 7, 8}, {0, 1, 2, 7, 8}, {0, 1, 2, 5, 8}, {0, 1, 2, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28304 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2931 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1860
    Fin15AnchoredAtom1996 Fin15AnchoredAtom2216 Fin15AnchoredAtom2931 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 7, 9}, {0, 2, 5, 7, 9}, {0, 1, 5, 7, 9}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28305 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1861
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2217 Fin15AnchoredAtom2932 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 7, 10}, {0, 2, 5, 7, 10}, {0, 1, 5, 7, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28306 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1848 Fin15AnchoredAtom1863
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2219 Fin15AnchoredAtom2934 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 7, 12}, {0, 2, 5, 7, 12}, {0, 1, 5, 7, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28307 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1849 Fin15AnchoredAtom1864
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2220 Fin15AnchoredAtom2935 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 7, 13}, {0, 2, 5, 7, 13}, {0, 1, 5, 7, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28308 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2936 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1850 Fin15AnchoredAtom1865
    Fin15AnchoredAtom2001 Fin15AnchoredAtom2221 Fin15AnchoredAtom2936 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 7, 14}, {0, 2, 5, 7, 14}, {0, 1, 5, 7, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28309 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1866 chi ∧
      Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2222 chi ∧
      Fin15AnchoredAtom2937 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1844 Fin15AnchoredAtom1845 Fin15AnchoredAtom1866
    Fin15AnchoredAtom2002 Fin15AnchoredAtom2222 Fin15AnchoredAtom2937 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 8, 9}, {0, 2, 5, 8, 9}, {0, 1, 5, 8, 9}, {0, 1, 2, 8, 9}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28310 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1872
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2228 Fin15AnchoredAtom2943 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 9, 10}, {0, 2, 5, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 2, 9, 10}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28311 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1845 Fin15AnchoredAtom1848 Fin15AnchoredAtom1874
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2230 Fin15AnchoredAtom2945 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 9, 12}, {0, 2, 5, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28312 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2946 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1845 Fin15AnchoredAtom1849 Fin15AnchoredAtom1875
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2231 Fin15AnchoredAtom2946 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 9, 13}, {0, 2, 5, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28313 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1845 Fin15AnchoredAtom1850 Fin15AnchoredAtom1876
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2232 Fin15AnchoredAtom2947 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 9, 14}, {0, 2, 5, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28314 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1846 Fin15AnchoredAtom1848 Fin15AnchoredAtom1878
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2234 Fin15AnchoredAtom2949 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 10, 12}, {0, 2, 5, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 2, 10, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28315 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1846 Fin15AnchoredAtom1849 Fin15AnchoredAtom1879
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2235 Fin15AnchoredAtom2950 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 10, 13}, {0, 2, 5, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28316 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1846 Fin15AnchoredAtom1850 Fin15AnchoredAtom1880
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2236 Fin15AnchoredAtom2951 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 10, 14}, {0, 2, 5, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28317 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1848 Fin15AnchoredAtom1849 Fin15AnchoredAtom1884
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2240 Fin15AnchoredAtom2955 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 12, 13}, {0, 2, 5, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 2, 12, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28318 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1848 Fin15AnchoredAtom1850 Fin15AnchoredAtom1885
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2241 Fin15AnchoredAtom2956 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 12, 14}, {0, 2, 5, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28319 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1849 Fin15AnchoredAtom1850 Fin15AnchoredAtom1886
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2242 Fin15AnchoredAtom2957 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 5, 13, 14}, {0, 2, 5, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 2, 13, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28320 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1852 chi ∧
      Fin15AnchoredAtom1859 chi ∧
      Fin15AnchoredAtom2023 chi ∧
      Fin15AnchoredAtom2243 chi ∧
      Fin15AnchoredAtom2958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1852 Fin15AnchoredAtom1859
    Fin15AnchoredAtom2023 Fin15AnchoredAtom2243 Fin15AnchoredAtom2958 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 7, 8}, {0, 2, 6, 7, 8}, {0, 1, 6, 7, 8}, {0, 1, 2, 7, 8}, {0, 1, 2, 6, 8}, {0, 1, 2, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28321 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1860
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2244 Fin15AnchoredAtom2959 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 7, 9}, {0, 2, 6, 7, 9}, {0, 1, 6, 7, 9}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28322 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1861
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2245 Fin15AnchoredAtom2960 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 7, 10}, {0, 2, 6, 7, 10}, {0, 1, 6, 7, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28323 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1863
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2247 Fin15AnchoredAtom2962 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 7, 12}, {0, 2, 6, 7, 12}, {0, 1, 6, 7, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28324 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1857 Fin15AnchoredAtom1864
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2248 Fin15AnchoredAtom2963 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 7, 13}, {0, 2, 6, 7, 13}, {0, 1, 6, 7, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28325 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1858 Fin15AnchoredAtom1865
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2249 Fin15AnchoredAtom2964 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 7, 14}, {0, 2, 6, 7, 14}, {0, 1, 6, 7, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28326 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1852 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1866 chi ∧
      Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2250 chi ∧
      Fin15AnchoredAtom2965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1852 Fin15AnchoredAtom1853 Fin15AnchoredAtom1866
    Fin15AnchoredAtom2030 Fin15AnchoredAtom2250 Fin15AnchoredAtom2965 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 8, 9}, {0, 2, 6, 8, 9}, {0, 1, 6, 8, 9}, {0, 1, 2, 8, 9}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28327 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1872
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2256 Fin15AnchoredAtom2971 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 9, 10}, {0, 2, 6, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28328 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1874
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2258 Fin15AnchoredAtom2973 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 9, 12}, {0, 2, 6, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28329 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1853 Fin15AnchoredAtom1857 Fin15AnchoredAtom1875
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2259 Fin15AnchoredAtom2974 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 9, 13}, {0, 2, 6, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28330 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1853 Fin15AnchoredAtom1858 Fin15AnchoredAtom1876
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2260 Fin15AnchoredAtom2975 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 9, 14}, {0, 2, 6, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28331 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1855 chi ∧
      Fin15AnchoredAtom1877 chi ∧
      Fin15AnchoredAtom2041 chi ∧
      Fin15AnchoredAtom2261 chi ∧
      Fin15AnchoredAtom2976 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1854 Fin15AnchoredAtom1855 Fin15AnchoredAtom1877
    Fin15AnchoredAtom2041 Fin15AnchoredAtom2261 Fin15AnchoredAtom2976 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 10, 11}, {0, 2, 6, 10, 11}, {0, 1, 6, 10, 11}, {0, 1, 2, 10, 11}, {0, 1, 2, 6, 11}, {0, 1, 2, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28332 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1878
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2262 Fin15AnchoredAtom2977 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 10, 12}, {0, 2, 6, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 2, 10, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28333 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1854 Fin15AnchoredAtom1857 Fin15AnchoredAtom1879
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2263 Fin15AnchoredAtom2978 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 10, 13}, {0, 2, 6, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28334 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1854 Fin15AnchoredAtom1858 Fin15AnchoredAtom1880
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2264 Fin15AnchoredAtom2979 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 10, 14}, {0, 2, 6, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28335 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1856 Fin15AnchoredAtom1857 Fin15AnchoredAtom1884
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2268 Fin15AnchoredAtom2983 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 12, 13}, {0, 2, 6, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 2, 12, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28336 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1856 Fin15AnchoredAtom1858 Fin15AnchoredAtom1885
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2269 Fin15AnchoredAtom2984 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 12, 14}, {0, 2, 6, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28337 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1857 Fin15AnchoredAtom1858 Fin15AnchoredAtom1886
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2270 Fin15AnchoredAtom2985 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 6, 13, 14}, {0, 2, 6, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 2, 13, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28338 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1872
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2277 Fin15AnchoredAtom2992 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 9, 10}, {0, 2, 7, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28339 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1874
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2279 Fin15AnchoredAtom2994 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 9, 12}, {0, 2, 7, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28340 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1875
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2280 Fin15AnchoredAtom2995 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 9, 13}, {0, 2, 7, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28341 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1860 Fin15AnchoredAtom1865 Fin15AnchoredAtom1876
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2281 Fin15AnchoredAtom2996 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 9, 14}, {0, 2, 7, 9, 14}, {0, 1, 7, 9, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28342 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1878
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2283 Fin15AnchoredAtom2998 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 10, 12}, {0, 2, 7, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28343 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1879
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2284 Fin15AnchoredAtom2999 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 10, 13}, {0, 2, 7, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28344 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom3000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1861 Fin15AnchoredAtom1865 Fin15AnchoredAtom1880
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2285 Fin15AnchoredAtom3000 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 10, 14}, {0, 2, 7, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28345 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom3004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1884
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2289 Fin15AnchoredAtom3004 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 12, 13}, {0, 2, 7, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 2, 12, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28346 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom3005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1863 Fin15AnchoredAtom1865 Fin15AnchoredAtom1885
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2290 Fin15AnchoredAtom3005 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 12, 14}, {0, 2, 7, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28347 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom3006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1864 Fin15AnchoredAtom1865 Fin15AnchoredAtom1886
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2291 Fin15AnchoredAtom3006 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 7, 13, 14}, {0, 2, 7, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 2, 13, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28348 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom3023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2308 Fin15AnchoredAtom3023 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 9, 10, 12}, {0, 2, 9, 10, 12}, {0, 1, 9, 10, 12}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28349 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom3024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2309 Fin15AnchoredAtom3024 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 9, 10, 13}, {0, 2, 9, 10, 13}, {0, 1, 9, 10, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28350 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom3025 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2310 Fin15AnchoredAtom3025 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 9, 10, 14}, {0, 2, 9, 10, 14}, {0, 1, 9, 10, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28351 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1873 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1881 chi ∧
      Fin15AnchoredAtom2091 chi ∧
      Fin15AnchoredAtom2311 chi ∧
      Fin15AnchoredAtom3026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1873 Fin15AnchoredAtom1874 Fin15AnchoredAtom1881
    Fin15AnchoredAtom2091 Fin15AnchoredAtom2311 Fin15AnchoredAtom3026 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 9, 11, 12}, {0, 2, 9, 11, 12}, {0, 1, 9, 11, 12}, {0, 1, 2, 11, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28352 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom3029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2314 Fin15AnchoredAtom3029 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 9, 12, 13}, {0, 2, 9, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28353 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom3030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2315 Fin15AnchoredAtom3030 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 9, 12, 14}, {0, 2, 9, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28354 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom3031 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2316 Fin15AnchoredAtom3031 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 9, 13, 14}, {0, 2, 9, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 2, 13, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28355 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom3035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2320 Fin15AnchoredAtom3035 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 10, 12, 13}, {0, 2, 10, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28356 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom3036 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2321 Fin15AnchoredAtom3036 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 10, 12, 14}, {0, 2, 10, 12, 14}, {0, 1, 10, 12, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28357 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom3037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2322 Fin15AnchoredAtom3037 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 10, 13, 14}, {0, 2, 10, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28358 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom3041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2326 Fin15AnchoredAtom3041 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 12, 13, 14}, {0, 2, 12, 13, 14}, {0, 1, 12, 13, 14}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28359 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom3042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1942 Fin15AnchoredAtom2327 Fin15AnchoredAtom3042 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 6}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 5, 6} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 5, 6} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 5, 6}, {0, 3, 4, 5, 6}, {0, 1, 4, 5, 6}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28360 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom3043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1943 Fin15AnchoredAtom2328 Fin15AnchoredAtom3043 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 5, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 5, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 5, 7}, {0, 3, 4, 5, 7}, {0, 1, 4, 5, 7}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28361 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1944 chi ∧
      Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom3044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1899
    Fin15AnchoredAtom1944 Fin15AnchoredAtom2329 Fin15AnchoredAtom3044 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 5, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 5, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 5, 8}, {0, 3, 4, 5, 8}, {0, 1, 4, 5, 8}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28362 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom3045 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1891 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1945 Fin15AnchoredAtom2330 Fin15AnchoredAtom3045 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 5, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 5, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 5, 9}, {0, 3, 4, 5, 9}, {0, 1, 4, 5, 9}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28363 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom3046 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1892 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1946 Fin15AnchoredAtom2331 Fin15AnchoredAtom3046 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 5, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 5, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 5, 10}, {0, 3, 4, 5, 10}, {0, 1, 4, 5, 10}, {0, 1, 3, 5, 10}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28364 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom3048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1894 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1948 Fin15AnchoredAtom2333 Fin15AnchoredAtom3048 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 5, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 5, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 5, 12}, {0, 3, 4, 5, 12}, {0, 1, 4, 5, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28365 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom3049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1895 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1949 Fin15AnchoredAtom2334 Fin15AnchoredAtom3049 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 5, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 5, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 5, 13}, {0, 3, 4, 5, 13}, {0, 1, 4, 5, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28366 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom3050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1896 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1950 Fin15AnchoredAtom2335 Fin15AnchoredAtom3050 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 5, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 5, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 5, 14}, {0, 3, 4, 5, 14}, {0, 1, 4, 5, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28367 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom3051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1951 Fin15AnchoredAtom2336 Fin15AnchoredAtom3051 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 6, 7}, {0, 3, 4, 6, 7}, {0, 1, 4, 6, 7}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28368 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom3052 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1890 Fin15AnchoredAtom1907
    Fin15AnchoredAtom1952 Fin15AnchoredAtom2337 Fin15AnchoredAtom3052 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 6, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 6, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 6, 8}, {0, 3, 4, 6, 8}, {0, 1, 4, 6, 8}, {0, 1, 3, 6, 8}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28369 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom3053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1891 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1953 Fin15AnchoredAtom2338 Fin15AnchoredAtom3053 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 6, 9}, {0, 3, 4, 6, 9}, {0, 1, 4, 6, 9}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28370 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom3054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1892 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1954 Fin15AnchoredAtom2339 Fin15AnchoredAtom3054 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 6, 10}, {0, 3, 4, 6, 10}, {0, 1, 4, 6, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28371 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom3056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1894 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1956 Fin15AnchoredAtom2341 Fin15AnchoredAtom3056 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 6, 12}, {0, 3, 4, 6, 12}, {0, 1, 4, 6, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28372 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom3057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1895 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1957 Fin15AnchoredAtom2342 Fin15AnchoredAtom3057 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 6, 13}, {0, 3, 4, 6, 13}, {0, 1, 4, 6, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28373 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom3058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1896 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1958 Fin15AnchoredAtom2343 Fin15AnchoredAtom3058 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 6, 14}, {0, 3, 4, 6, 14}, {0, 1, 4, 6, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28374 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1959 chi ∧
      Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom3059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1890 Fin15AnchoredAtom1914
    Fin15AnchoredAtom1959 Fin15AnchoredAtom2344 Fin15AnchoredAtom3059 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 7, 8}, {0, 3, 4, 7, 8}, {0, 1, 4, 7, 8}, {0, 1, 3, 7, 8}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28375 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom3060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1915
    Fin15AnchoredAtom1960 Fin15AnchoredAtom2345 Fin15AnchoredAtom3060 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 7, 9}, {0, 3, 4, 7, 9}, {0, 1, 4, 7, 9}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28376 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom3061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1892 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1961 Fin15AnchoredAtom2346 Fin15AnchoredAtom3061 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 7, 10}, {0, 3, 4, 7, 10}, {0, 1, 4, 7, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28377 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom3063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1894 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1963 Fin15AnchoredAtom2348 Fin15AnchoredAtom3063 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 7, 12}, {0, 3, 4, 7, 12}, {0, 1, 4, 7, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28378 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom3064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1895 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1964 Fin15AnchoredAtom2349 Fin15AnchoredAtom3064 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 7, 13}, {0, 3, 4, 7, 13}, {0, 1, 4, 7, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28379 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom3065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1896 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1965 Fin15AnchoredAtom2350 Fin15AnchoredAtom3065 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 7, 14}, {0, 3, 4, 7, 14}, {0, 1, 4, 7, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28380 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom3066 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1890 Fin15AnchoredAtom1891 Fin15AnchoredAtom1921
    Fin15AnchoredAtom1966 Fin15AnchoredAtom2351 Fin15AnchoredAtom3066 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 8, 9}, {0, 3, 4, 8, 9}, {0, 1, 4, 8, 9}, {0, 1, 3, 8, 9}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28381 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom3067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1890 Fin15AnchoredAtom1892 Fin15AnchoredAtom1922
    Fin15AnchoredAtom1967 Fin15AnchoredAtom2352 Fin15AnchoredAtom3067 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 8, 10}, {0, 3, 4, 8, 10}, {0, 1, 4, 8, 10}, {0, 1, 3, 8, 10}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28382 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom3069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1890 Fin15AnchoredAtom1894 Fin15AnchoredAtom1924
    Fin15AnchoredAtom1969 Fin15AnchoredAtom2354 Fin15AnchoredAtom3069 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 8, 12}, {0, 3, 4, 8, 12}, {0, 1, 4, 8, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28383 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom3070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1890 Fin15AnchoredAtom1895 Fin15AnchoredAtom1925
    Fin15AnchoredAtom1970 Fin15AnchoredAtom2355 Fin15AnchoredAtom3070 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 8, 13}, {0, 3, 4, 8, 13}, {0, 1, 4, 8, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28384 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom3071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1890 Fin15AnchoredAtom1896 Fin15AnchoredAtom1926
    Fin15AnchoredAtom1971 Fin15AnchoredAtom2356 Fin15AnchoredAtom3071 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 8, 14}, {0, 3, 4, 8, 14}, {0, 1, 4, 8, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28385 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom3072 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1891 Fin15AnchoredAtom1892 Fin15AnchoredAtom1927
    Fin15AnchoredAtom1972 Fin15AnchoredAtom2357 Fin15AnchoredAtom3072 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 9, 10}, {0, 3, 4, 9, 10}, {0, 1, 4, 9, 10}, {0, 1, 3, 9, 10}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28386 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom3074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1891 Fin15AnchoredAtom1894 Fin15AnchoredAtom1929
    Fin15AnchoredAtom1974 Fin15AnchoredAtom2359 Fin15AnchoredAtom3074 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 9, 12}, {0, 3, 4, 9, 12}, {0, 1, 4, 9, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28387 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom3075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1891 Fin15AnchoredAtom1895 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1975 Fin15AnchoredAtom2360 Fin15AnchoredAtom3075 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 9, 13}, {0, 3, 4, 9, 13}, {0, 1, 4, 9, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28388 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom3076 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1891 Fin15AnchoredAtom1896 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1976 Fin15AnchoredAtom2361 Fin15AnchoredAtom3076 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 9, 14}, {0, 3, 4, 9, 14}, {0, 1, 4, 9, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28389 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom3078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1892 Fin15AnchoredAtom1894 Fin15AnchoredAtom1933
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2363 Fin15AnchoredAtom3078 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 10, 12}, {0, 3, 4, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28390 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom3079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1892 Fin15AnchoredAtom1895 Fin15AnchoredAtom1934
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2364 Fin15AnchoredAtom3079 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 10, 13}, {0, 3, 4, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28391 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom3080 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1892 Fin15AnchoredAtom1896 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2365 Fin15AnchoredAtom3080 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 10, 14}, {0, 3, 4, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28392 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1893 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1936 chi ∧
      Fin15AnchoredAtom1981 chi ∧
      Fin15AnchoredAtom2366 chi ∧
      Fin15AnchoredAtom3081 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1893 Fin15AnchoredAtom1894 Fin15AnchoredAtom1936
    Fin15AnchoredAtom1981 Fin15AnchoredAtom2366 Fin15AnchoredAtom3081 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 11, 12}, {0, 3, 4, 11, 12}, {0, 1, 4, 11, 12}, {0, 1, 3, 11, 12}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28393 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom3084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1894 Fin15AnchoredAtom1895 Fin15AnchoredAtom1939
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2369 Fin15AnchoredAtom3084 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 12, 13}, {0, 3, 4, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 3, 12, 13}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28394 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom3085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1894 Fin15AnchoredAtom1896 Fin15AnchoredAtom1940
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2370 Fin15AnchoredAtom3085 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 12, 14}, {0, 3, 4, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28395 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom3086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1895 Fin15AnchoredAtom1896 Fin15AnchoredAtom1941
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2371 Fin15AnchoredAtom3086 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 4, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 4, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 4, 13, 14}, {0, 3, 4, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 3, 13, 14}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28396 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom3087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1987 Fin15AnchoredAtom2372 Fin15AnchoredAtom3087 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 6, 7}, {0, 3, 5, 6, 7}, {0, 1, 5, 6, 7}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28397 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom3088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1899 Fin15AnchoredAtom1907
    Fin15AnchoredAtom1988 Fin15AnchoredAtom2373 Fin15AnchoredAtom3088 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 6, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 6, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 6, 8}, {0, 3, 5, 6, 8}, {0, 1, 5, 6, 8}, {0, 1, 3, 6, 8}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28398 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom3089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1989 Fin15AnchoredAtom2374 Fin15AnchoredAtom3089 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 6, 9}, {0, 3, 5, 6, 9}, {0, 1, 5, 6, 9}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28399 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom3090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1901 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1990 Fin15AnchoredAtom2375 Fin15AnchoredAtom3090 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 6, 10}, {0, 3, 5, 6, 10}, {0, 1, 5, 6, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28400 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom3092 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1903 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1992 Fin15AnchoredAtom2377 Fin15AnchoredAtom3092 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 6, 12}, {0, 3, 5, 6, 12}, {0, 1, 5, 6, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28401 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom3093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1904 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1993 Fin15AnchoredAtom2378 Fin15AnchoredAtom3093 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 6, 13}, {0, 3, 5, 6, 13}, {0, 1, 5, 6, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28402 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom3094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1905 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1994 Fin15AnchoredAtom2379 Fin15AnchoredAtom3094 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 6, 14}, {0, 3, 5, 6, 14}, {0, 1, 5, 6, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28403 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1995 chi ∧
      Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom3095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1914
    Fin15AnchoredAtom1995 Fin15AnchoredAtom2380 Fin15AnchoredAtom3095 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 7, 8}, {0, 3, 5, 7, 8}, {0, 1, 5, 7, 8}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28404 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom3096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1915
    Fin15AnchoredAtom1996 Fin15AnchoredAtom2381 Fin15AnchoredAtom3096 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 7, 9}, {0, 3, 5, 7, 9}, {0, 1, 5, 7, 9}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28405 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom3097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1901 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2382 Fin15AnchoredAtom3097 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 7, 10}, {0, 3, 5, 7, 10}, {0, 1, 5, 7, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28406 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom3099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1903 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2384 Fin15AnchoredAtom3099 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 7, 12}, {0, 3, 5, 7, 12}, {0, 1, 5, 7, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28407 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom3100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1904 Fin15AnchoredAtom1919
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2385 Fin15AnchoredAtom3100 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 7, 13}, {0, 3, 5, 7, 13}, {0, 1, 5, 7, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28408 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom3101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1905 Fin15AnchoredAtom1920
    Fin15AnchoredAtom2001 Fin15AnchoredAtom2386 Fin15AnchoredAtom3101 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 7, 14}, {0, 3, 5, 7, 14}, {0, 1, 5, 7, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28409 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom3102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1899 Fin15AnchoredAtom1900 Fin15AnchoredAtom1921
    Fin15AnchoredAtom2002 Fin15AnchoredAtom2387 Fin15AnchoredAtom3102 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 8, 9}, {0, 3, 5, 8, 9}, {0, 1, 5, 8, 9}, {0, 1, 3, 8, 9}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28410 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom2003 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom3103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1899 Fin15AnchoredAtom1901 Fin15AnchoredAtom1922
    Fin15AnchoredAtom2003 Fin15AnchoredAtom2388 Fin15AnchoredAtom3103 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 8, 10}, {0, 3, 5, 8, 10}, {0, 1, 5, 8, 10}, {0, 1, 3, 8, 10}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28411 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom2005 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom3105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1899 Fin15AnchoredAtom1903 Fin15AnchoredAtom1924
    Fin15AnchoredAtom2005 Fin15AnchoredAtom2390 Fin15AnchoredAtom3105 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 8, 12}, {0, 3, 5, 8, 12}, {0, 1, 5, 8, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28412 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom2007 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom3107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1899 Fin15AnchoredAtom1905 Fin15AnchoredAtom1926
    Fin15AnchoredAtom2007 Fin15AnchoredAtom2392 Fin15AnchoredAtom3107 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 8, 14}, {0, 3, 5, 8, 14}, {0, 1, 5, 8, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28413 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom3108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1927
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2393 Fin15AnchoredAtom3108 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 9, 10}, {0, 3, 5, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28414 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom3110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1900 Fin15AnchoredAtom1903 Fin15AnchoredAtom1929
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2395 Fin15AnchoredAtom3110 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 9, 12}, {0, 3, 5, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28415 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom3111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1900 Fin15AnchoredAtom1904 Fin15AnchoredAtom1930
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2396 Fin15AnchoredAtom3111 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 9, 13}, {0, 3, 5, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

end ErdosSzekeres

end
