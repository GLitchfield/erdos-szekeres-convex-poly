module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 223. -/

theorem fin15Anchored_clause28544 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom3329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1990 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2614 Fin15AnchoredAtom3329 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 7, 10}, {0, 5, 6, 7, 10}, {0, 1, 6, 7, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28545 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom3331 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1992 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2616 Fin15AnchoredAtom3331 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 7, 12}, {0, 5, 6, 7, 12}, {0, 1, 6, 7, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28546 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom3332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1993 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2617 Fin15AnchoredAtom3332 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 7, 13}, {0, 5, 6, 7, 13}, {0, 1, 6, 7, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28547 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom3333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1994 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2618 Fin15AnchoredAtom3333 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 7, 14}, {0, 5, 6, 7, 14}, {0, 1, 6, 7, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28548 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom3334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1988 Fin15AnchoredAtom1989 Fin15AnchoredAtom2002
    Fin15AnchoredAtom2030 Fin15AnchoredAtom2619 Fin15AnchoredAtom3334 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 8, 9}, {0, 5, 6, 8, 9}, {0, 1, 6, 8, 9}, {0, 1, 5, 8, 9}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28549 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2003 chi ∧
      Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2620 chi ∧
      Fin15AnchoredAtom3335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1988 Fin15AnchoredAtom1990 Fin15AnchoredAtom2003
    Fin15AnchoredAtom2031 Fin15AnchoredAtom2620 Fin15AnchoredAtom3335 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 8, 10}, {0, 5, 6, 8, 10}, {0, 1, 6, 8, 10}, {0, 1, 5, 8, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28550 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom3340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2625 Fin15AnchoredAtom3340 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 9, 10}, {0, 5, 6, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28551 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom3342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1989 Fin15AnchoredAtom1992 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2627 Fin15AnchoredAtom3342 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 9, 12}, {0, 5, 6, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28552 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom3343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1989 Fin15AnchoredAtom1993 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2628 Fin15AnchoredAtom3343 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 9, 13}, {0, 5, 6, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28553 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom3344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1989 Fin15AnchoredAtom1994 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2629 Fin15AnchoredAtom3344 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 9, 14}, {0, 5, 6, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28554 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom3346 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2631 Fin15AnchoredAtom3346 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 10, 12}, {0, 5, 6, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28555 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom3347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2632 Fin15AnchoredAtom3347 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 10, 13}, {0, 5, 6, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28556 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom3348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2633 Fin15AnchoredAtom3348 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 10, 14}, {0, 5, 6, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28557 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom3352 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2637 Fin15AnchoredAtom3352 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 12, 13}, {0, 5, 6, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28558 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom3353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2638 Fin15AnchoredAtom3353 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 12, 14}, {0, 5, 6, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28559 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom3354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2639 Fin15AnchoredAtom3354 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 13, 14}, {0, 5, 6, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28560 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1995 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom3355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1995 Fin15AnchoredAtom1996 Fin15AnchoredAtom2002
    Fin15AnchoredAtom2051 Fin15AnchoredAtom2640 Fin15AnchoredAtom3355 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 8, 9}, {0, 5, 7, 8, 9}, {0, 1, 7, 8, 9}, {0, 1, 5, 8, 9}, {0, 1, 5, 7, 9}, {0, 1, 5, 7, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28561 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom3361 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2646 Fin15AnchoredAtom3361 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28562 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom3363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1996 Fin15AnchoredAtom1999 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2648 Fin15AnchoredAtom3363 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28563 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom3364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1996 Fin15AnchoredAtom2000 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2649 Fin15AnchoredAtom3364 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28564 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom3365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1996 Fin15AnchoredAtom2001 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2650 Fin15AnchoredAtom3365 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 1, 7, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28565 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom3367 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2652 Fin15AnchoredAtom3367 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28566 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom3368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2653 Fin15AnchoredAtom3368 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28567 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom3369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1997 Fin15AnchoredAtom2001 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2654 Fin15AnchoredAtom3369 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28568 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom3373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2658 Fin15AnchoredAtom3373 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28569 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom3374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2659 Fin15AnchoredAtom3374 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28570 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom3375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2660 Fin15AnchoredAtom3375 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28571 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2006 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom3379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2002 Fin15AnchoredAtom2006 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2664 Fin15AnchoredAtom3379 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 8, 9, 13}, {0, 5, 8, 9, 13}, {0, 1, 8, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28572 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2003 chi ∧
      Fin15AnchoredAtom2006 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom3383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2003 Fin15AnchoredAtom2006 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2668 Fin15AnchoredAtom3383 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 8, 10, 13}, {0, 5, 8, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28573 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2005 chi ∧
      Fin15AnchoredAtom2006 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom3388 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2005 Fin15AnchoredAtom2006 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2084 Fin15AnchoredAtom2673 Fin15AnchoredAtom3388 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 8, 12, 13}, {0, 5, 8, 12, 13}, {0, 1, 8, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28574 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2005 chi ∧
      Fin15AnchoredAtom2007 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom3389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2005 Fin15AnchoredAtom2007 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2674 Fin15AnchoredAtom3389 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 8, 12, 14}, {0, 5, 8, 12, 14}, {0, 1, 8, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28575 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom3392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2677 Fin15AnchoredAtom3392 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 1, 9, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28576 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom3393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2008 Fin15AnchoredAtom2011 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2678 Fin15AnchoredAtom3393 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 1, 9, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28577 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom3394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2008 Fin15AnchoredAtom2012 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2679 Fin15AnchoredAtom3394 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 1, 9, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28578 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom3398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2683 Fin15AnchoredAtom3398 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28579 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom3399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2010 Fin15AnchoredAtom2012 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2684 Fin15AnchoredAtom3399 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28580 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom3400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2685 Fin15AnchoredAtom3400 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28581 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2013 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2018 chi ∧
      Fin15AnchoredAtom2098 chi ∧
      Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom3402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2013 Fin15AnchoredAtom2015 Fin15AnchoredAtom2018
    Fin15AnchoredAtom2098 Fin15AnchoredAtom2687 Fin15AnchoredAtom3402 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 10, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 10, 11, 13}, {0, 5, 10, 11, 13}, {0, 1, 10, 11, 13}, {0, 1, 5, 11, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28582 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom3404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2689 Fin15AnchoredAtom3404 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28583 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom3405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2014 Fin15AnchoredAtom2016 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2690 Fin15AnchoredAtom3405 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 1, 10, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28584 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom3406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2691 Fin15AnchoredAtom3406 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28585 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom3410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2695 Fin15AnchoredAtom3410 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 1, 12, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28586 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom3417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2702 Fin15AnchoredAtom3417 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 9, 10}, {0, 6, 7, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28587 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom3419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2704 Fin15AnchoredAtom3419 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 9, 12}, {0, 6, 7, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28588 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom3420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2705 Fin15AnchoredAtom3420 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 9, 13}, {0, 6, 7, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28589 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom3421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2024 Fin15AnchoredAtom2029 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2706 Fin15AnchoredAtom3421 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 9, 14}, {0, 6, 7, 9, 14}, {0, 1, 7, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28590 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom3423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2708 Fin15AnchoredAtom3423 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 10, 12}, {0, 6, 7, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28591 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom3424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2709 Fin15AnchoredAtom3424 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 10, 13}, {0, 6, 7, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28592 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom3425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2710 Fin15AnchoredAtom3425 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 10, 14}, {0, 6, 7, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28593 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom3429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2714 Fin15AnchoredAtom3429 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 12, 13}, {0, 6, 7, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28594 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom3430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2715 Fin15AnchoredAtom3430 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 12, 14}, {0, 6, 7, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28595 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom3431 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2716 Fin15AnchoredAtom3431 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 7, 13, 14}, {0, 6, 7, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28596 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom3432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2030 Fin15AnchoredAtom2031 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2717 Fin15AnchoredAtom3432 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 8, 9, 10}, {0, 6, 8, 9, 10}, {0, 1, 8, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 6, 8, 10}, {0, 1, 6, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28597 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom3434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2030 Fin15AnchoredAtom2033 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2719 Fin15AnchoredAtom3434 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 8, 9, 12}, {0, 6, 8, 9, 12}, {0, 1, 8, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28598 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom3435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2030 Fin15AnchoredAtom2034 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2720 Fin15AnchoredAtom3435 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 8, 9, 13}, {0, 6, 8, 9, 13}, {0, 1, 8, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28599 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom3439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2031 Fin15AnchoredAtom2034 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2724 Fin15AnchoredAtom3439 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 8, 10, 13}, {0, 6, 8, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28600 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom3444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2033 Fin15AnchoredAtom2034 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2084 Fin15AnchoredAtom2729 Fin15AnchoredAtom3444 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 8, 12, 13}, {0, 6, 8, 12, 13}, {0, 1, 8, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28601 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom2035 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom3445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2033 Fin15AnchoredAtom2035 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2730 Fin15AnchoredAtom3445 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 8, 12, 14}, {0, 6, 8, 12, 14}, {0, 1, 8, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28602 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom2035 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom3446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2034 Fin15AnchoredAtom2035 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2731 Fin15AnchoredAtom3446 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 8, 13, 14}, {0, 6, 8, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28603 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom3448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2733 Fin15AnchoredAtom3448 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 1, 9, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28604 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom3449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2036 Fin15AnchoredAtom2039 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2734 Fin15AnchoredAtom3449 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 1, 9, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28605 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom3450 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2036 Fin15AnchoredAtom2040 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2735 Fin15AnchoredAtom3450 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 1, 9, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28606 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom3454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2739 Fin15AnchoredAtom3454 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28607 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom3455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2740 Fin15AnchoredAtom3455 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28608 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom3456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2741 Fin15AnchoredAtom3456 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28609 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom3460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2745 Fin15AnchoredAtom3460 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28610 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom3461 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2042 Fin15AnchoredAtom2044 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2746 Fin15AnchoredAtom3461 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 1, 10, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28611 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom3462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2747 Fin15AnchoredAtom3462 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28612 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom3466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2751 Fin15AnchoredAtom3466 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 6, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 1, 12, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28613 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2052 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom3467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2051 Fin15AnchoredAtom2052 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2752 Fin15AnchoredAtom3467 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 8, 9, 10}, {0, 7, 8, 9, 10}, {0, 1, 8, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 7, 8, 10}, {0, 1, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28614 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2054 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom3469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2051 Fin15AnchoredAtom2054 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2754 Fin15AnchoredAtom3469 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 8, 9, 12}, {0, 7, 8, 9, 12}, {0, 1, 8, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28615 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2055 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom3470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2051 Fin15AnchoredAtom2055 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2755 Fin15AnchoredAtom3470 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 8, 9, 13}, {0, 7, 8, 9, 13}, {0, 1, 8, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28616 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom3471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2051 Fin15AnchoredAtom2056 Fin15AnchoredAtom2061
    Fin15AnchoredAtom2076 Fin15AnchoredAtom2756 Fin15AnchoredAtom3471 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 8, 9, 14}, {0, 7, 8, 9, 14}, {0, 1, 8, 9, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28617 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2052 chi ∧
      Fin15AnchoredAtom2054 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom3473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2052 Fin15AnchoredAtom2054 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2758 Fin15AnchoredAtom3473 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 8, 10, 12}, {0, 7, 8, 10, 12}, {0, 1, 8, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28618 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2054 chi ∧
      Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom3480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2054 Fin15AnchoredAtom2056 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2765 Fin15AnchoredAtom3480 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 8, 12, 14}, {0, 7, 8, 12, 14}, {0, 1, 8, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28619 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2055 chi ∧
      Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom3481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2766 Fin15AnchoredAtom3481 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 8, 13, 14}, {0, 7, 8, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28620 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom3483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2768 Fin15AnchoredAtom3483 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 1, 9, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28621 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom3484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2769 Fin15AnchoredAtom3484 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 1, 9, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28622 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom3485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2770 Fin15AnchoredAtom3485 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 1, 9, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28623 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom3489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2774 Fin15AnchoredAtom3489 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28624 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom3490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2775 Fin15AnchoredAtom3490 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28625 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom3491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2776 Fin15AnchoredAtom3491 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 9, 13, 14}, {0, 7, 9, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28626 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom3495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2780 Fin15AnchoredAtom3495 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28627 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom3496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2781 Fin15AnchoredAtom3496 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 1, 10, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28628 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom3497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2782 Fin15AnchoredAtom3497 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28629 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom3501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2786 Fin15AnchoredAtom3501 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 7, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 1, 12, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28630 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom3503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2072 Fin15AnchoredAtom2074 Fin15AnchoredAtom2078
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2788 Fin15AnchoredAtom3503 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 8, 9, 10, 12}, {0, 8, 9, 10, 12}, {0, 1, 9, 10, 12}, {0, 1, 8, 10, 12}, {0, 1, 8, 9, 12}, {0, 1, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28631 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom3504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2072 Fin15AnchoredAtom2075 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2789 Fin15AnchoredAtom3504 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 8, 9, 10, 13}, {0, 8, 9, 10, 13}, {0, 1, 9, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 8, 9, 13}, {0, 1, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28632 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom3510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2074 Fin15AnchoredAtom2076 Fin15AnchoredAtom2085
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2795 Fin15AnchoredAtom3510 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 8, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 8, 9, 12, 14}, {0, 8, 9, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 8, 12, 14}, {0, 1, 8, 9, 14}, {0, 1, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28633 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom3511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2075 Fin15AnchoredAtom2076 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2796 Fin15AnchoredAtom3511 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 8, 9, 13, 14}, {0, 8, 9, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 8, 9, 14}, {0, 1, 8, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28634 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom3515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2078 Fin15AnchoredAtom2079 Fin15AnchoredAtom2084
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2800 Fin15AnchoredAtom3515 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 8, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 8, 12, 13}, {0, 1, 8, 10, 13}, {0, 1, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28635 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom3516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2078 Fin15AnchoredAtom2080 Fin15AnchoredAtom2085
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2801 Fin15AnchoredAtom3516 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 8, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 1, 10, 12, 14}, {0, 1, 8, 12, 14}, {0, 1, 8, 10, 14}, {0, 1, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28636 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom3517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2079 Fin15AnchoredAtom2080 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2802 Fin15AnchoredAtom3517 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 8, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 8, 10, 14}, {0, 1, 8, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28637 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom3521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2084 Fin15AnchoredAtom2085 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2806 Fin15AnchoredAtom3521 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 8, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 1, 12, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 8, 12, 14}, {0, 1, 8, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28638 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom3525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2810 Fin15AnchoredAtom3525 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 9, 10, 12, 13}, {0, 9, 10, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28639 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom3526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2811 Fin15AnchoredAtom3526 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 9, 10, 12, 14}, {0, 9, 10, 12, 14}, {0, 1, 10, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28640 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom3527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2812 Fin15AnchoredAtom3527 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 9, 10, 13, 14}, {0, 9, 10, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28641 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom3531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2816 Fin15AnchoredAtom3531 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 9, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 1, 12, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28642 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2097 chi ∧
      Fin15AnchoredAtom2098 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2103 chi ∧
      Fin15AnchoredAtom2817 chi ∧
      Fin15AnchoredAtom3532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2097 Fin15AnchoredAtom2098 Fin15AnchoredAtom2100
    Fin15AnchoredAtom2103 Fin15AnchoredAtom2817 Fin15AnchoredAtom3532 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 10, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 10, 11, 12, 13}, {0, 10, 11, 12, 13}, {0, 1, 11, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 10, 11, 13}, {0, 1, 10, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28643 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom3535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2820 Fin15AnchoredAtom3535 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 10, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28644 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom3537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2117
    Fin15AnchoredAtom2162 Fin15AnchoredAtom2327 Fin15AnchoredAtom3537 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 6}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 5, 6} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 5, 6} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 6}, {0, 3, 4, 5, 6}, {0, 2, 4, 5, 6}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28645 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom3538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2118
    Fin15AnchoredAtom2163 Fin15AnchoredAtom2328 Fin15AnchoredAtom3538 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 5, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 5, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 7}, {0, 3, 4, 5, 7}, {0, 2, 4, 5, 7}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28646 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom3540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2120
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2330 Fin15AnchoredAtom3540 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 5, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 5, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 9}, {0, 3, 4, 5, 9}, {0, 2, 4, 5, 9}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28647 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom3541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2112 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2331 Fin15AnchoredAtom3541 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 5, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 5, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 10}, {0, 3, 4, 5, 10}, {0, 2, 4, 5, 10}, {0, 2, 3, 5, 10}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28648 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2113 chi ∧
      Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom2167 chi ∧
      Fin15AnchoredAtom2332 chi ∧
      Fin15AnchoredAtom3542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2113 Fin15AnchoredAtom2122
    Fin15AnchoredAtom2167 Fin15AnchoredAtom2332 Fin15AnchoredAtom3542 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 5, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 5, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 11}, {0, 3, 4, 5, 11}, {0, 2, 4, 5, 11}, {0, 2, 3, 5, 11}, {0, 2, 3, 4, 11}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28649 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom3543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2114 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2333 Fin15AnchoredAtom3543 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 5, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 5, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 12}, {0, 3, 4, 5, 12}, {0, 2, 4, 5, 12}, {0, 2, 3, 5, 12}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28650 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom3544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2115 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2334 Fin15AnchoredAtom3544 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 5, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 5, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 13}, {0, 3, 4, 5, 13}, {0, 2, 4, 5, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28651 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom3545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2116 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2170 Fin15AnchoredAtom2335 Fin15AnchoredAtom3545 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 5, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 5, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 14}, {0, 3, 4, 5, 14}, {0, 2, 4, 5, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28652 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom3546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2126
    Fin15AnchoredAtom2171 Fin15AnchoredAtom2336 Fin15AnchoredAtom3546 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 7}, {0, 3, 4, 6, 7}, {0, 2, 4, 6, 7}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28653 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom3548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2128
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2338 Fin15AnchoredAtom3548 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 9}, {0, 3, 4, 6, 9}, {0, 2, 4, 6, 9}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28654 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom3549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2112 Fin15AnchoredAtom2129
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2339 Fin15AnchoredAtom3549 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 10}, {0, 3, 4, 6, 10}, {0, 2, 4, 6, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28655 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom3551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2114 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2341 Fin15AnchoredAtom3551 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 12}, {0, 3, 4, 6, 12}, {0, 2, 4, 6, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28656 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom3552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2115 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2342 Fin15AnchoredAtom3552 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 13}, {0, 3, 4, 6, 13}, {0, 2, 4, 6, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28657 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom3553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2116 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2178 Fin15AnchoredAtom2343 Fin15AnchoredAtom3553 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 14}, {0, 3, 4, 6, 14}, {0, 2, 4, 6, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28658 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2110 chi ∧
      Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2179 chi ∧
      Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom3554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2110 Fin15AnchoredAtom2134
    Fin15AnchoredAtom2179 Fin15AnchoredAtom2344 Fin15AnchoredAtom3554 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 8}, {0, 3, 4, 7, 8}, {0, 2, 4, 7, 8}, {0, 2, 3, 7, 8}, {0, 2, 3, 4, 8}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28659 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom3555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2135
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2345 Fin15AnchoredAtom3555 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 9}, {0, 3, 4, 7, 9}, {0, 2, 4, 7, 9}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28660 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom3556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2112 Fin15AnchoredAtom2136
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2346 Fin15AnchoredAtom3556 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 10}, {0, 3, 4, 7, 10}, {0, 2, 4, 7, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28661 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2113 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2182 chi ∧
      Fin15AnchoredAtom2347 chi ∧
      Fin15AnchoredAtom3557 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2113 Fin15AnchoredAtom2137
    Fin15AnchoredAtom2182 Fin15AnchoredAtom2347 Fin15AnchoredAtom3557 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 7, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 7, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 7, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 11}, {0, 3, 4, 7, 11}, {0, 2, 4, 7, 11}, {0, 2, 3, 7, 11}, {0, 2, 3, 4, 11}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28662 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom3558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2114 Fin15AnchoredAtom2138
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2348 Fin15AnchoredAtom3558 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 12}, {0, 3, 4, 7, 12}, {0, 2, 4, 7, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28663 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom3559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2115 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2349 Fin15AnchoredAtom3559 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 13}, {0, 3, 4, 7, 13}, {0, 2, 4, 7, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28664 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom3560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2116 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2185 Fin15AnchoredAtom2350 Fin15AnchoredAtom3560 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 14}, {0, 3, 4, 7, 14}, {0, 2, 4, 7, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28665 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2110 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom2186 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom3561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2110 Fin15AnchoredAtom2111 Fin15AnchoredAtom2141
    Fin15AnchoredAtom2186 Fin15AnchoredAtom2351 Fin15AnchoredAtom3561 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 8, 9}, {0, 3, 4, 8, 9}, {0, 2, 4, 8, 9}, {0, 2, 3, 8, 9}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28666 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2110 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2187 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom3562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2110 Fin15AnchoredAtom2112 Fin15AnchoredAtom2142
    Fin15AnchoredAtom2187 Fin15AnchoredAtom2352 Fin15AnchoredAtom3562 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 8, 10}, {0, 3, 4, 8, 10}, {0, 2, 4, 8, 10}, {0, 2, 3, 8, 10}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28667 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom3567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2112 Fin15AnchoredAtom2147
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2357 Fin15AnchoredAtom3567 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 9, 10}, {0, 3, 4, 9, 10}, {0, 2, 4, 9, 10}, {0, 2, 3, 9, 10}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28668 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom3569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2114 Fin15AnchoredAtom2149
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2359 Fin15AnchoredAtom3569 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 9, 12}, {0, 3, 4, 9, 12}, {0, 2, 4, 9, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28669 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom3570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2115 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2360 Fin15AnchoredAtom3570 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 9, 13}, {0, 3, 4, 9, 13}, {0, 2, 4, 9, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28670 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom3571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2116 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2196 Fin15AnchoredAtom2361 Fin15AnchoredAtom3571 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 9, 14}, {0, 3, 4, 9, 14}, {0, 2, 4, 9, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause28671 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom3573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2112 Fin15AnchoredAtom2114 Fin15AnchoredAtom2153
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2363 Fin15AnchoredAtom3573 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 10, 12}, {0, 3, 4, 10, 12}, {0, 2, 4, 10, 12}, {0, 2, 3, 10, 12}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}] : List (Finset (Fin 15))) :
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
