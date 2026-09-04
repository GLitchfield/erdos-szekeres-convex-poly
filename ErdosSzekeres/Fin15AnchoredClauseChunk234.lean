module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 234. -/

theorem fin15Anchored_clause29952 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom4179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3588 Fin15AnchoredAtom3589 Fin15AnchoredAtom3617
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3849 Fin15AnchoredAtom4179 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 13, 14}, {2, 5, 6, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29953 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom4186 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3652 Fin15AnchoredAtom3856 Fin15AnchoredAtom4186 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 10}, {2, 5, 7, 9, 10}, {2, 3, 7, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29954 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom4188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3591 Fin15AnchoredAtom3594 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3858 Fin15AnchoredAtom4188 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 12}, {2, 5, 7, 9, 12}, {2, 3, 7, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29955 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom4189 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3591 Fin15AnchoredAtom3595 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3859 Fin15AnchoredAtom4189 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 13}, {2, 5, 7, 9, 13}, {2, 3, 7, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29956 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom4190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3591 Fin15AnchoredAtom3596 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3656 Fin15AnchoredAtom3860 Fin15AnchoredAtom4190 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 14}, {2, 5, 7, 9, 14}, {2, 3, 7, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29957 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom4192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3592 Fin15AnchoredAtom3594 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3658 Fin15AnchoredAtom3862 Fin15AnchoredAtom4192 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 12}, {2, 5, 7, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29958 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom4193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3592 Fin15AnchoredAtom3595 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3863 Fin15AnchoredAtom4193 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 13}, {2, 5, 7, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29959 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom4194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3592 Fin15AnchoredAtom3596 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3864 Fin15AnchoredAtom4194 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 14}, {2, 5, 7, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29960 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom4198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3594 Fin15AnchoredAtom3595 Fin15AnchoredAtom3615
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3868 Fin15AnchoredAtom4198 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 12, 13}, {2, 5, 7, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29961 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom4199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3594 Fin15AnchoredAtom3596 Fin15AnchoredAtom3616
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3869 Fin15AnchoredAtom4199 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 12, 14}, {2, 5, 7, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29962 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom4200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3595 Fin15AnchoredAtom3596 Fin15AnchoredAtom3617
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3870 Fin15AnchoredAtom4200 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 13, 14}, {2, 5, 7, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29963 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom4217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3603 Fin15AnchoredAtom3605 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3683 Fin15AnchoredAtom3887 Fin15AnchoredAtom4217 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 3, 9, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29964 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom4218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3603 Fin15AnchoredAtom3606 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3888 Fin15AnchoredAtom4218 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 3, 9, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29965 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom4219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3603 Fin15AnchoredAtom3607 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3889 Fin15AnchoredAtom4219 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 3, 9, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29966 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom4223 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3605 Fin15AnchoredAtom3606 Fin15AnchoredAtom3615
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3893 Fin15AnchoredAtom4223 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29967 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom4224 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3605 Fin15AnchoredAtom3607 Fin15AnchoredAtom3616
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3894 Fin15AnchoredAtom4224 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29968 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom4225 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3606 Fin15AnchoredAtom3607 Fin15AnchoredAtom3617
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3895 Fin15AnchoredAtom4225 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29969 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3608 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3613 chi ∧
      Fin15AnchoredAtom3693 chi ∧
      Fin15AnchoredAtom3897 chi ∧
      Fin15AnchoredAtom4227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3608 Fin15AnchoredAtom3610 Fin15AnchoredAtom3613
    Fin15AnchoredAtom3693 Fin15AnchoredAtom3897 Fin15AnchoredAtom4227 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 10, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 11, 13}, {2, 5, 10, 11, 13}, {2, 3, 10, 11, 13}, {2, 3, 5, 11, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29970 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom4229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3609 Fin15AnchoredAtom3610 Fin15AnchoredAtom3615
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3899 Fin15AnchoredAtom4229 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29971 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom4230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3609 Fin15AnchoredAtom3611 Fin15AnchoredAtom3616
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3900 Fin15AnchoredAtom4230 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29972 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom4231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3610 Fin15AnchoredAtom3611 Fin15AnchoredAtom3617
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3901 Fin15AnchoredAtom4231 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29973 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom4235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3615 Fin15AnchoredAtom3616 Fin15AnchoredAtom3617
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3905 Fin15AnchoredAtom4235 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29974 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom4242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3619 Fin15AnchoredAtom3620 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3652 Fin15AnchoredAtom3912 Fin15AnchoredAtom4242 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 10}, {2, 6, 7, 9, 10}, {2, 3, 7, 9, 10}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29975 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom4244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3619 Fin15AnchoredAtom3622 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3914 Fin15AnchoredAtom4244 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 12}, {2, 6, 7, 9, 12}, {2, 3, 7, 9, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29976 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom4245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3619 Fin15AnchoredAtom3623 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3915 Fin15AnchoredAtom4245 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 13}, {2, 6, 7, 9, 13}, {2, 3, 7, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29977 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom4246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3619 Fin15AnchoredAtom3624 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3656 Fin15AnchoredAtom3916 Fin15AnchoredAtom4246 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 14}, {2, 6, 7, 9, 14}, {2, 3, 7, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29978 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3621 chi ∧
      Fin15AnchoredAtom3636 chi ∧
      Fin15AnchoredAtom3657 chi ∧
      Fin15AnchoredAtom3917 chi ∧
      Fin15AnchoredAtom4247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3620 Fin15AnchoredAtom3621 Fin15AnchoredAtom3636
    Fin15AnchoredAtom3657 Fin15AnchoredAtom3917 Fin15AnchoredAtom4247 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 11}, {2, 6, 7, 10, 11}, {2, 3, 7, 10, 11}, {2, 3, 6, 10, 11}, {2, 3, 6, 7, 11}, {2, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29979 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom4248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3620 Fin15AnchoredAtom3622 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3658 Fin15AnchoredAtom3918 Fin15AnchoredAtom4248 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 12}, {2, 6, 7, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29980 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom4249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3620 Fin15AnchoredAtom3623 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3919 Fin15AnchoredAtom4249 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 13}, {2, 6, 7, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29981 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom4250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3620 Fin15AnchoredAtom3624 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3920 Fin15AnchoredAtom4250 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 14}, {2, 6, 7, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29982 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom4254 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3622 Fin15AnchoredAtom3623 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3924 Fin15AnchoredAtom4254 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 12, 13}, {2, 6, 7, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29983 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom4255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3622 Fin15AnchoredAtom3624 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3925 Fin15AnchoredAtom4255 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 12, 14}, {2, 6, 7, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29984 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom4256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3645
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3926 Fin15AnchoredAtom4256 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 13, 14}, {2, 6, 7, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29985 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom4273 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3631 Fin15AnchoredAtom3633 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3683 Fin15AnchoredAtom3943 Fin15AnchoredAtom4273 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 3, 9, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29986 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom4274 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3631 Fin15AnchoredAtom3634 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3944 Fin15AnchoredAtom4274 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 3, 9, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29987 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom4275 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3631 Fin15AnchoredAtom3635 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3945 Fin15AnchoredAtom4275 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 3, 9, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29988 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom4279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3633 Fin15AnchoredAtom3634 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3949 Fin15AnchoredAtom4279 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29989 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom4280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3633 Fin15AnchoredAtom3635 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3950 Fin15AnchoredAtom4280 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29990 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom4281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3634 Fin15AnchoredAtom3635 Fin15AnchoredAtom3645
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3951 Fin15AnchoredAtom4281 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29991 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3636 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3640 chi ∧
      Fin15AnchoredAtom3692 chi ∧
      Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom4282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3636 Fin15AnchoredAtom3637 Fin15AnchoredAtom3640
    Fin15AnchoredAtom3692 Fin15AnchoredAtom3952 Fin15AnchoredAtom4282 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 11, 12}, {2, 6, 10, 11, 12}, {2, 3, 10, 11, 12}, {2, 3, 6, 11, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29992 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom4285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3637 Fin15AnchoredAtom3638 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3955 Fin15AnchoredAtom4285 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29993 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom4286 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3637 Fin15AnchoredAtom3639 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3956 Fin15AnchoredAtom4286 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29994 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom4287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3638 Fin15AnchoredAtom3639 Fin15AnchoredAtom3645
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3957 Fin15AnchoredAtom4287 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29995 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3640 chi ∧
      Fin15AnchoredAtom3641 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3698 chi ∧
      Fin15AnchoredAtom3958 chi ∧
      Fin15AnchoredAtom4288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3640 Fin15AnchoredAtom3641 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3698 Fin15AnchoredAtom3958 Fin15AnchoredAtom4288 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 11, 12, 13}, {2, 6, 11, 12, 13}, {2, 3, 11, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 11, 13}, {2, 3, 6, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29996 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3643 Fin15AnchoredAtom3644 Fin15AnchoredAtom3645
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3961 Fin15AnchoredAtom4291 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29997 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom4308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3652 Fin15AnchoredAtom3654 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3683 Fin15AnchoredAtom3978 Fin15AnchoredAtom4308 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 12}, {2, 7, 9, 10, 12}, {2, 3, 9, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29998 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom4309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3652 Fin15AnchoredAtom3655 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3979 Fin15AnchoredAtom4309 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 13}, {2, 7, 9, 10, 13}, {2, 3, 9, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29999 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom4310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3652 Fin15AnchoredAtom3656 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3980 Fin15AnchoredAtom4310 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 14}, {2, 7, 9, 10, 14}, {2, 3, 9, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30000 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom4314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3654 Fin15AnchoredAtom3655 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3984 Fin15AnchoredAtom4314 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 12, 13}, {2, 7, 9, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30001 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom4315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3654 Fin15AnchoredAtom3656 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3985 Fin15AnchoredAtom4315 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 12, 14}, {2, 7, 9, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30002 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom4316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3986 Fin15AnchoredAtom4316 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 13, 14}, {2, 7, 9, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30003 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3658 Fin15AnchoredAtom3659 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3990 Fin15AnchoredAtom4320 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30004 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3658 Fin15AnchoredAtom3660 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3991 Fin15AnchoredAtom4321 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30005 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3659 Fin15AnchoredAtom3660 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3992 Fin15AnchoredAtom4322 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30006 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3664 Fin15AnchoredAtom3665 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3996 Fin15AnchoredAtom4326 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30007 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3682 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3686 chi ∧
      Fin15AnchoredAtom3692 chi ∧
      Fin15AnchoredAtom4017 chi ∧
      Fin15AnchoredAtom4347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3682 Fin15AnchoredAtom3683 Fin15AnchoredAtom3686
    Fin15AnchoredAtom3692 Fin15AnchoredAtom4017 Fin15AnchoredAtom4347 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 9, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 11, 12}, {2, 9, 10, 11, 12}, {2, 3, 10, 11, 12}, {2, 3, 9, 11, 12}, {2, 3, 9, 10, 12}, {2, 3, 9, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30008 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3683 Fin15AnchoredAtom3684 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3695 Fin15AnchoredAtom4020 Fin15AnchoredAtom4350 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 12, 13}, {2, 9, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30009 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3683 Fin15AnchoredAtom3685 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3696 Fin15AnchoredAtom4021 Fin15AnchoredAtom4351 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 12, 14}, {2, 9, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30010 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4352 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3697 Fin15AnchoredAtom4022 Fin15AnchoredAtom4352 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 13, 14}, {2, 9, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30011 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3689 Fin15AnchoredAtom3690 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3701 Fin15AnchoredAtom4026 Fin15AnchoredAtom4356 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30012 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom4030 Fin15AnchoredAtom4360 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 10, 12, 14}, {2, 3, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30013 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom4363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3711
    Fin15AnchoredAtom3739 Fin15AnchoredAtom3823 Fin15AnchoredAtom4363 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 9}, {2, 5, 6, 7, 9}, {2, 4, 6, 7, 9}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30014 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom4364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3712
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3824 Fin15AnchoredAtom4364 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 10}, {2, 5, 6, 7, 10}, {2, 4, 6, 7, 10}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30015 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom4366 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3707 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3826 Fin15AnchoredAtom4366 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 12}, {2, 5, 6, 7, 12}, {2, 4, 6, 7, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30016 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom4367 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3708 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3827 Fin15AnchoredAtom4367 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 13}, {2, 5, 6, 7, 13}, {2, 4, 6, 7, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30017 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom4368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3709 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3828 Fin15AnchoredAtom4368 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 14}, {2, 5, 6, 7, 14}, {2, 4, 6, 7, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30018 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom4375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3751 Fin15AnchoredAtom3835 Fin15AnchoredAtom4375 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 10}, {2, 5, 6, 9, 10}, {2, 4, 6, 9, 10}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30019 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom4377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3704 Fin15AnchoredAtom3707 Fin15AnchoredAtom3725
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3837 Fin15AnchoredAtom4377 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 12}, {2, 5, 6, 9, 12}, {2, 4, 6, 9, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30020 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom4378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3704 Fin15AnchoredAtom3708 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3838 Fin15AnchoredAtom4378 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 13}, {2, 5, 6, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30021 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom4379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3704 Fin15AnchoredAtom3709 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3839 Fin15AnchoredAtom4379 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 14}, {2, 5, 6, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30022 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom4381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3705 Fin15AnchoredAtom3707 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3841 Fin15AnchoredAtom4381 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 12}, {2, 5, 6, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30023 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom4382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3705 Fin15AnchoredAtom3708 Fin15AnchoredAtom3730
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3842 Fin15AnchoredAtom4382 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 13}, {2, 5, 6, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30024 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom4383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3705 Fin15AnchoredAtom3709 Fin15AnchoredAtom3731
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3843 Fin15AnchoredAtom4383 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 14}, {2, 5, 6, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30025 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom4387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3707 Fin15AnchoredAtom3708 Fin15AnchoredAtom3735
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3847 Fin15AnchoredAtom4387 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 13}, {2, 5, 6, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30026 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom4388 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3707 Fin15AnchoredAtom3709 Fin15AnchoredAtom3736
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3848 Fin15AnchoredAtom4388 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 14}, {2, 5, 6, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30027 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom4389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3708 Fin15AnchoredAtom3709 Fin15AnchoredAtom3737
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3849 Fin15AnchoredAtom4389 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 13, 14}, {2, 5, 6, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30028 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom4396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3772 Fin15AnchoredAtom3856 Fin15AnchoredAtom4396 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 10}, {2, 5, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30029 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom4398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3714 Fin15AnchoredAtom3725
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3858 Fin15AnchoredAtom4398 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 12}, {2, 5, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30030 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom4399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3715 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3859 Fin15AnchoredAtom4399 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 13}, {2, 5, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30031 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom4400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3716 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3860 Fin15AnchoredAtom4400 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 14}, {2, 5, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30032 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom4402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3778 Fin15AnchoredAtom3862 Fin15AnchoredAtom4402 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 12}, {2, 5, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30033 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom4403 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3712 Fin15AnchoredAtom3715 Fin15AnchoredAtom3730
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3863 Fin15AnchoredAtom4403 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 13}, {2, 5, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30034 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom4404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3712 Fin15AnchoredAtom3716 Fin15AnchoredAtom3731
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3864 Fin15AnchoredAtom4404 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 14}, {2, 5, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30035 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom4408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3714 Fin15AnchoredAtom3715 Fin15AnchoredAtom3735
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3868 Fin15AnchoredAtom4408 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 13}, {2, 5, 7, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30036 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom4409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3714 Fin15AnchoredAtom3716 Fin15AnchoredAtom3736
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3869 Fin15AnchoredAtom4409 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 14}, {2, 5, 7, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30037 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom4410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3715 Fin15AnchoredAtom3716 Fin15AnchoredAtom3737
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3870 Fin15AnchoredAtom4410 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 13, 14}, {2, 5, 7, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30038 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom4427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3803 Fin15AnchoredAtom3887 Fin15AnchoredAtom4427 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30039 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom4428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3723 Fin15AnchoredAtom3726 Fin15AnchoredAtom3730
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3888 Fin15AnchoredAtom4428 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30040 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom4429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3723 Fin15AnchoredAtom3727 Fin15AnchoredAtom3731
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3889 Fin15AnchoredAtom4429 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30041 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom4433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3725 Fin15AnchoredAtom3726 Fin15AnchoredAtom3735
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3893 Fin15AnchoredAtom4433 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30042 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom4434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3725 Fin15AnchoredAtom3727 Fin15AnchoredAtom3736
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3894 Fin15AnchoredAtom4434 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30043 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom4435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3726 Fin15AnchoredAtom3727 Fin15AnchoredAtom3737
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3895 Fin15AnchoredAtom4435 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30044 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom4439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3735
    Fin15AnchoredAtom3815 Fin15AnchoredAtom3899 Fin15AnchoredAtom4439 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30045 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom4440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3729 Fin15AnchoredAtom3731 Fin15AnchoredAtom3736
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3900 Fin15AnchoredAtom4440 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30046 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom4441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3730 Fin15AnchoredAtom3731 Fin15AnchoredAtom3737
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3901 Fin15AnchoredAtom4441 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30047 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom4445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3905 Fin15AnchoredAtom4445 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30048 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3738 chi ∧
      Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3745 chi ∧
      Fin15AnchoredAtom3766 chi ∧
      Fin15AnchoredAtom3906 chi ∧
      Fin15AnchoredAtom4446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3738 Fin15AnchoredAtom3739 Fin15AnchoredAtom3745
    Fin15AnchoredAtom3766 Fin15AnchoredAtom3906 Fin15AnchoredAtom4446 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 9}, {2, 6, 7, 8, 9}, {2, 4, 7, 8, 9}, {2, 4, 6, 8, 9}, {2, 4, 6, 7, 9}, {2, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30049 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom4452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3772 Fin15AnchoredAtom3912 Fin15AnchoredAtom4452 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 10}, {2, 6, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30050 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3741 chi ∧
      Fin15AnchoredAtom3752 chi ∧
      Fin15AnchoredAtom3773 chi ∧
      Fin15AnchoredAtom3913 chi ∧
      Fin15AnchoredAtom4453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3741 Fin15AnchoredAtom3752
    Fin15AnchoredAtom3773 Fin15AnchoredAtom3913 Fin15AnchoredAtom4453 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 9, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 11}, {2, 6, 7, 9, 11}, {2, 4, 7, 9, 11}, {2, 4, 6, 9, 11}, {2, 4, 6, 7, 11}, {2, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30051 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom4454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3742 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3914 Fin15AnchoredAtom4454 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 12}, {2, 6, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30052 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom4455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3743 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3915 Fin15AnchoredAtom4455 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 13}, {2, 6, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30053 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom4456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3744 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3916 Fin15AnchoredAtom4456 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 14}, {2, 6, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30054 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom4458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3740 Fin15AnchoredAtom3742 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3778 Fin15AnchoredAtom3918 Fin15AnchoredAtom4458 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 12}, {2, 6, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30055 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom4459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3740 Fin15AnchoredAtom3743 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3919 Fin15AnchoredAtom4459 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 13}, {2, 6, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30056 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom4460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3740 Fin15AnchoredAtom3744 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3920 Fin15AnchoredAtom4460 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 14}, {2, 6, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30057 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom4464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3742 Fin15AnchoredAtom3743 Fin15AnchoredAtom3763
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3924 Fin15AnchoredAtom4464 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 13}, {2, 6, 7, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30058 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom4465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3742 Fin15AnchoredAtom3744 Fin15AnchoredAtom3764
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3925 Fin15AnchoredAtom4465 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 14}, {2, 6, 7, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30059 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom4466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3743 Fin15AnchoredAtom3744 Fin15AnchoredAtom3765
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3926 Fin15AnchoredAtom4466 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 13, 14}, {2, 6, 7, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30060 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom4483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3751 Fin15AnchoredAtom3753 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3803 Fin15AnchoredAtom3943 Fin15AnchoredAtom4483 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30061 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom4484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3751 Fin15AnchoredAtom3754 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3944 Fin15AnchoredAtom4484 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30062 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom4485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3751 Fin15AnchoredAtom3755 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3945 Fin15AnchoredAtom4485 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30063 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom4489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3753 Fin15AnchoredAtom3754 Fin15AnchoredAtom3763
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3949 Fin15AnchoredAtom4489 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30064 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom4490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3753 Fin15AnchoredAtom3755 Fin15AnchoredAtom3764
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3950 Fin15AnchoredAtom4490 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30065 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom4491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3754 Fin15AnchoredAtom3755 Fin15AnchoredAtom3765
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3951 Fin15AnchoredAtom4491 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30066 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom4495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3757 Fin15AnchoredAtom3758 Fin15AnchoredAtom3763
    Fin15AnchoredAtom3815 Fin15AnchoredAtom3955 Fin15AnchoredAtom4495 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30067 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom4496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3757 Fin15AnchoredAtom3759 Fin15AnchoredAtom3764
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3956 Fin15AnchoredAtom4496 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30068 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom4497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3758 Fin15AnchoredAtom3759 Fin15AnchoredAtom3765
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3957 Fin15AnchoredAtom4497 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30069 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3763 Fin15AnchoredAtom3764 Fin15AnchoredAtom3765
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3961 Fin15AnchoredAtom4501 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30070 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom4518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3772 Fin15AnchoredAtom3774 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3803 Fin15AnchoredAtom3978 Fin15AnchoredAtom4518 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 12}, {2, 7, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 7, 9, 12}, {2, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30071 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom4519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3772 Fin15AnchoredAtom3775 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3979 Fin15AnchoredAtom4519 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 13}, {2, 7, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30072 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom4520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3772 Fin15AnchoredAtom3776 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3980 Fin15AnchoredAtom4520 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 14}, {2, 7, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30073 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom4524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3774 Fin15AnchoredAtom3775 Fin15AnchoredAtom3784
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3984 Fin15AnchoredAtom4524 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 13}, {2, 7, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30074 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom4525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3774 Fin15AnchoredAtom3776 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3985 Fin15AnchoredAtom4525 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 14}, {2, 7, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30075 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom4526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3775 Fin15AnchoredAtom3776 Fin15AnchoredAtom3786
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3986 Fin15AnchoredAtom4526 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 13, 14}, {2, 7, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30076 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3778 Fin15AnchoredAtom3779 Fin15AnchoredAtom3784
    Fin15AnchoredAtom3815 Fin15AnchoredAtom3990 Fin15AnchoredAtom4530 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30077 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3778 Fin15AnchoredAtom3780 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3991 Fin15AnchoredAtom4531 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30078 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3779 Fin15AnchoredAtom3780 Fin15AnchoredAtom3786
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3992 Fin15AnchoredAtom4532 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30079 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3784 Fin15AnchoredAtom3785 Fin15AnchoredAtom3786
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3996 Fin15AnchoredAtom4536 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 12, 13}] : List (Finset (Fin 15))) :
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
