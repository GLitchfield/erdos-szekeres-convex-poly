module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 235. -/

theorem fin15Anchored_clause30080 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3787 chi ∧
      Fin15AnchoredAtom3789 chi ∧
      Fin15AnchoredAtom3793 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3998 chi ∧
      Fin15AnchoredAtom4538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3787 Fin15AnchoredAtom3789 Fin15AnchoredAtom3793
    Fin15AnchoredAtom3803 Fin15AnchoredAtom3998 Fin15AnchoredAtom4538 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 10, 12}, {2, 8, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 8, 10, 12}, {2, 4, 8, 9, 12}, {2, 4, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30081 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3793 chi ∧
      Fin15AnchoredAtom3794 chi ∧
      Fin15AnchoredAtom3799 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom4010 chi ∧
      Fin15AnchoredAtom4550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3793 Fin15AnchoredAtom3794 Fin15AnchoredAtom3799
    Fin15AnchoredAtom3815 Fin15AnchoredAtom4010 Fin15AnchoredAtom4550 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 10, 12, 13}, {2, 8, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 8, 12, 13}, {2, 4, 8, 10, 13}, {2, 4, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30082 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3803 Fin15AnchoredAtom3804 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3815 Fin15AnchoredAtom4020 Fin15AnchoredAtom4560 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 13}, {2, 9, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30083 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3803 Fin15AnchoredAtom3805 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3816 Fin15AnchoredAtom4021 Fin15AnchoredAtom4561 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 14}, {2, 9, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30084 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3804 Fin15AnchoredAtom3805 Fin15AnchoredAtom3811
    Fin15AnchoredAtom3817 Fin15AnchoredAtom4022 Fin15AnchoredAtom4562 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 13, 14}, {2, 9, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30085 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3809 Fin15AnchoredAtom3810 Fin15AnchoredAtom3811
    Fin15AnchoredAtom3821 Fin15AnchoredAtom4026 Fin15AnchoredAtom4566 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30086 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3815 Fin15AnchoredAtom3816 Fin15AnchoredAtom3817
    Fin15AnchoredAtom3821 Fin15AnchoredAtom4030 Fin15AnchoredAtom4570 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 4, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30087 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom4578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3856 Fin15AnchoredAtom3912 Fin15AnchoredAtom4578 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {2, 6, 7, 9, 10}, {2, 5, 7, 9, 10}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30088 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom4580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3823 Fin15AnchoredAtom3826 Fin15AnchoredAtom3837
    Fin15AnchoredAtom3858 Fin15AnchoredAtom3914 Fin15AnchoredAtom4580 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {2, 6, 7, 9, 12}, {2, 5, 7, 9, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30089 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom4581 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3823 Fin15AnchoredAtom3827 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3915 Fin15AnchoredAtom4581 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {2, 6, 7, 9, 13}, {2, 5, 7, 9, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30090 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom4582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3823 Fin15AnchoredAtom3828 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3916 Fin15AnchoredAtom4582 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {2, 6, 7, 9, 14}, {2, 5, 7, 9, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30091 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3825 chi ∧
      Fin15AnchoredAtom3840 chi ∧
      Fin15AnchoredAtom3861 chi ∧
      Fin15AnchoredAtom3917 chi ∧
      Fin15AnchoredAtom4583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3824 Fin15AnchoredAtom3825 Fin15AnchoredAtom3840
    Fin15AnchoredAtom3861 Fin15AnchoredAtom3917 Fin15AnchoredAtom4583 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 11}, {2, 6, 7, 10, 11}, {2, 5, 7, 10, 11}, {2, 5, 6, 10, 11}, {2, 5, 6, 7, 11}, {2, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30092 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom4584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3824 Fin15AnchoredAtom3826 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3918 Fin15AnchoredAtom4584 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {2, 6, 7, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30093 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom4585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3824 Fin15AnchoredAtom3827 Fin15AnchoredAtom3842
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3919 Fin15AnchoredAtom4585 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {2, 6, 7, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30094 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom4586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3824 Fin15AnchoredAtom3828 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3920 Fin15AnchoredAtom4586 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {2, 6, 7, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30095 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom4590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3826 Fin15AnchoredAtom3827 Fin15AnchoredAtom3847
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3924 Fin15AnchoredAtom4590 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {2, 6, 7, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30096 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom4591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3826 Fin15AnchoredAtom3828 Fin15AnchoredAtom3848
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3925 Fin15AnchoredAtom4591 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {2, 6, 7, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30097 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom4592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3827 Fin15AnchoredAtom3828 Fin15AnchoredAtom3849
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3926 Fin15AnchoredAtom4592 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {2, 6, 7, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30098 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom4609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3887 Fin15AnchoredAtom3943 Fin15AnchoredAtom4609 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30099 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom4610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3835 Fin15AnchoredAtom3838 Fin15AnchoredAtom3842
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3944 Fin15AnchoredAtom4610 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30100 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom4611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3835 Fin15AnchoredAtom3839 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3945 Fin15AnchoredAtom4611 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30101 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom4615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3837 Fin15AnchoredAtom3838 Fin15AnchoredAtom3847
    Fin15AnchoredAtom3893 Fin15AnchoredAtom3949 Fin15AnchoredAtom4615 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30102 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom4616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3837 Fin15AnchoredAtom3839 Fin15AnchoredAtom3848
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3950 Fin15AnchoredAtom4616 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30103 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom4617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3838 Fin15AnchoredAtom3839 Fin15AnchoredAtom3849
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3951 Fin15AnchoredAtom4617 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30104 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3840 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3844 chi ∧
      Fin15AnchoredAtom3896 chi ∧
      Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom4618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3840 Fin15AnchoredAtom3841 Fin15AnchoredAtom3844
    Fin15AnchoredAtom3896 Fin15AnchoredAtom3952 Fin15AnchoredAtom4618 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 11, 12}, {2, 6, 10, 11, 12}, {2, 5, 10, 11, 12}, {2, 5, 6, 11, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30105 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom4621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3847
    Fin15AnchoredAtom3899 Fin15AnchoredAtom3955 Fin15AnchoredAtom4621 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30106 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom4622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3841 Fin15AnchoredAtom3843 Fin15AnchoredAtom3848
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3956 Fin15AnchoredAtom4622 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30107 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom4623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3842 Fin15AnchoredAtom3843 Fin15AnchoredAtom3849
    Fin15AnchoredAtom3901 Fin15AnchoredAtom3957 Fin15AnchoredAtom4623 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30108 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849
    Fin15AnchoredAtom3905 Fin15AnchoredAtom3961 Fin15AnchoredAtom4627 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30109 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom4644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3856 Fin15AnchoredAtom3858 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3887 Fin15AnchoredAtom3978 Fin15AnchoredAtom4644 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {2, 7, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30110 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom4645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3856 Fin15AnchoredAtom3859 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3979 Fin15AnchoredAtom4645 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {2, 7, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30111 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom4646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3856 Fin15AnchoredAtom3860 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3980 Fin15AnchoredAtom4646 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {2, 7, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30112 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom4650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3858 Fin15AnchoredAtom3859 Fin15AnchoredAtom3868
    Fin15AnchoredAtom3893 Fin15AnchoredAtom3984 Fin15AnchoredAtom4650 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {2, 7, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30113 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom4651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3858 Fin15AnchoredAtom3860 Fin15AnchoredAtom3869
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3985 Fin15AnchoredAtom4651 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {2, 7, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30114 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom4652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3859 Fin15AnchoredAtom3860 Fin15AnchoredAtom3870
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3986 Fin15AnchoredAtom4652 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {2, 7, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30115 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3862 Fin15AnchoredAtom3863 Fin15AnchoredAtom3868
    Fin15AnchoredAtom3899 Fin15AnchoredAtom3990 Fin15AnchoredAtom4656 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30116 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3862 Fin15AnchoredAtom3864 Fin15AnchoredAtom3869
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3991 Fin15AnchoredAtom4657 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30117 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3863 Fin15AnchoredAtom3864 Fin15AnchoredAtom3870
    Fin15AnchoredAtom3901 Fin15AnchoredAtom3992 Fin15AnchoredAtom4658 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30118 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3868 Fin15AnchoredAtom3869 Fin15AnchoredAtom3870
    Fin15AnchoredAtom3905 Fin15AnchoredAtom3996 Fin15AnchoredAtom4662 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30119 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3887 Fin15AnchoredAtom3888 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3899 Fin15AnchoredAtom4020 Fin15AnchoredAtom4686 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {2, 9, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30120 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3887 Fin15AnchoredAtom3889 Fin15AnchoredAtom3894
    Fin15AnchoredAtom3900 Fin15AnchoredAtom4021 Fin15AnchoredAtom4687 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {2, 9, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30121 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3888 Fin15AnchoredAtom3889 Fin15AnchoredAtom3895
    Fin15AnchoredAtom3901 Fin15AnchoredAtom4022 Fin15AnchoredAtom4688 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {2, 9, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30122 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3893 Fin15AnchoredAtom3894 Fin15AnchoredAtom3895
    Fin15AnchoredAtom3905 Fin15AnchoredAtom4026 Fin15AnchoredAtom4692 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30123 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3899 Fin15AnchoredAtom3900 Fin15AnchoredAtom3901
    Fin15AnchoredAtom3905 Fin15AnchoredAtom4030 Fin15AnchoredAtom4696 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 5, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30124 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom4714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3943 Fin15AnchoredAtom3978 Fin15AnchoredAtom4714 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {2, 7, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 6, 7, 10, 12}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30125 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom4715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3912 Fin15AnchoredAtom3915 Fin15AnchoredAtom3919
    Fin15AnchoredAtom3944 Fin15AnchoredAtom3979 Fin15AnchoredAtom4715 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {2, 7, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30126 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom4716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3912 Fin15AnchoredAtom3916 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3980 Fin15AnchoredAtom4716 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {2, 7, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30127 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3913 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom3921 chi ∧
      Fin15AnchoredAtom3946 chi ∧
      Fin15AnchoredAtom3981 chi ∧
      Fin15AnchoredAtom4717 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3913 Fin15AnchoredAtom3914 Fin15AnchoredAtom3921
    Fin15AnchoredAtom3946 Fin15AnchoredAtom3981 Fin15AnchoredAtom4717 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 11, 12}, {2, 7, 9, 11, 12}, {2, 6, 9, 11, 12}, {2, 6, 7, 11, 12}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30128 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom4720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3914 Fin15AnchoredAtom3915 Fin15AnchoredAtom3924
    Fin15AnchoredAtom3949 Fin15AnchoredAtom3984 Fin15AnchoredAtom4720 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {2, 7, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30129 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom4721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3914 Fin15AnchoredAtom3916 Fin15AnchoredAtom3925
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3985 Fin15AnchoredAtom4721 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {2, 7, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30130 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom4722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3915 Fin15AnchoredAtom3916 Fin15AnchoredAtom3926
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3986 Fin15AnchoredAtom4722 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {2, 7, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30131 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3917 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom3922 chi ∧
      Fin15AnchoredAtom3953 chi ∧
      Fin15AnchoredAtom3988 chi ∧
      Fin15AnchoredAtom4724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3917 Fin15AnchoredAtom3919 Fin15AnchoredAtom3922
    Fin15AnchoredAtom3953 Fin15AnchoredAtom3988 Fin15AnchoredAtom4724 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 10, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 11, 13}, {2, 7, 10, 11, 13}, {2, 6, 10, 11, 13}, {2, 6, 7, 11, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30132 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3918 Fin15AnchoredAtom3919 Fin15AnchoredAtom3924
    Fin15AnchoredAtom3955 Fin15AnchoredAtom3990 Fin15AnchoredAtom4726 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30133 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3918 Fin15AnchoredAtom3920 Fin15AnchoredAtom3925
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3991 Fin15AnchoredAtom4727 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30134 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3919 Fin15AnchoredAtom3920 Fin15AnchoredAtom3926
    Fin15AnchoredAtom3957 Fin15AnchoredAtom3992 Fin15AnchoredAtom4728 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30135 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3924 Fin15AnchoredAtom3925 Fin15AnchoredAtom3926
    Fin15AnchoredAtom3961 Fin15AnchoredAtom3996 Fin15AnchoredAtom4732 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30136 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3942 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom3946 chi ∧
      Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom4017 chi ∧
      Fin15AnchoredAtom4753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3942 Fin15AnchoredAtom3943 Fin15AnchoredAtom3946
    Fin15AnchoredAtom3952 Fin15AnchoredAtom4017 Fin15AnchoredAtom4753 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 9, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 11, 12}, {2, 9, 10, 11, 12}, {2, 6, 10, 11, 12}, {2, 6, 9, 11, 12}, {2, 6, 9, 10, 12}, {2, 6, 9, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30137 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3943 Fin15AnchoredAtom3944 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3955 Fin15AnchoredAtom4020 Fin15AnchoredAtom4756 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {2, 9, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 9, 10, 13}, {2, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30138 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3943 Fin15AnchoredAtom3945 Fin15AnchoredAtom3950
    Fin15AnchoredAtom3956 Fin15AnchoredAtom4021 Fin15AnchoredAtom4757 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {2, 9, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30139 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3944 Fin15AnchoredAtom3945 Fin15AnchoredAtom3951
    Fin15AnchoredAtom3957 Fin15AnchoredAtom4022 Fin15AnchoredAtom4758 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {2, 9, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30140 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3946 chi ∧
      Fin15AnchoredAtom3947 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom3958 chi ∧
      Fin15AnchoredAtom4023 chi ∧
      Fin15AnchoredAtom4759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3946 Fin15AnchoredAtom3947 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3958 Fin15AnchoredAtom4023 Fin15AnchoredAtom4759 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 9, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 9, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 9, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 11, 12, 13}, {2, 9, 11, 12, 13}, {2, 6, 11, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 9, 11, 13}, {2, 6, 9, 11, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30141 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3949 Fin15AnchoredAtom3950 Fin15AnchoredAtom3951
    Fin15AnchoredAtom3961 Fin15AnchoredAtom4026 Fin15AnchoredAtom4762 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30142 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom3953 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom3958 chi ∧
      Fin15AnchoredAtom4027 chi ∧
      Fin15AnchoredAtom4763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3952 Fin15AnchoredAtom3953 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3958 Fin15AnchoredAtom4027 Fin15AnchoredAtom4763 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 10, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 11, 12, 13}, {2, 10, 11, 12, 13}, {2, 6, 11, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 10, 11, 13}, {2, 6, 10, 11, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30143 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3955 Fin15AnchoredAtom3956 Fin15AnchoredAtom3957
    Fin15AnchoredAtom3961 Fin15AnchoredAtom4030 Fin15AnchoredAtom4766 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 6, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 10, 12, 14}, {2, 6, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30144 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3977 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom3981 chi ∧
      Fin15AnchoredAtom3987 chi ∧
      Fin15AnchoredAtom4017 chi ∧
      Fin15AnchoredAtom4788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3977 Fin15AnchoredAtom3978 Fin15AnchoredAtom3981
    Fin15AnchoredAtom3987 Fin15AnchoredAtom4017 Fin15AnchoredAtom4788 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 7, 9, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 7, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 7, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 11, 12}, {2, 9, 10, 11, 12}, {2, 7, 10, 11, 12}, {2, 7, 9, 11, 12}, {2, 7, 9, 10, 12}, {2, 7, 9, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30145 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3978 Fin15AnchoredAtom3979 Fin15AnchoredAtom3984
    Fin15AnchoredAtom3990 Fin15AnchoredAtom4020 Fin15AnchoredAtom4791 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 7, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {2, 9, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 7, 9, 12, 13}, {2, 7, 9, 10, 13}, {2, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30146 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3978 Fin15AnchoredAtom3980 Fin15AnchoredAtom3985
    Fin15AnchoredAtom3991 Fin15AnchoredAtom4021 Fin15AnchoredAtom4792 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 7, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {2, 9, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30147 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3979 Fin15AnchoredAtom3980 Fin15AnchoredAtom3986
    Fin15AnchoredAtom3992 Fin15AnchoredAtom4022 Fin15AnchoredAtom4793 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 7, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {2, 9, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30148 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3984 Fin15AnchoredAtom3985 Fin15AnchoredAtom3986
    Fin15AnchoredAtom3996 Fin15AnchoredAtom4026 Fin15AnchoredAtom4797 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 7, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30149 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3988 chi ∧
      Fin15AnchoredAtom3989 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom3995 chi ∧
      Fin15AnchoredAtom4029 chi ∧
      Fin15AnchoredAtom4800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3988 Fin15AnchoredAtom3989 Fin15AnchoredAtom3992
    Fin15AnchoredAtom3995 Fin15AnchoredAtom4029 Fin15AnchoredAtom4800 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 7, 10, 11, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 7, 10, 11, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 7, 10, 11, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 11, 13, 14}, {2, 10, 11, 13, 14}, {2, 7, 11, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 10, 11, 14}, {2, 7, 10, 11, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30150 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3990 Fin15AnchoredAtom3991 Fin15AnchoredAtom3992
    Fin15AnchoredAtom3996 Fin15AnchoredAtom4030 Fin15AnchoredAtom4801 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 7, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 10, 12, 14}, {2, 7, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30151 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4020 Fin15AnchoredAtom4021 Fin15AnchoredAtom4022
    Fin15AnchoredAtom4026 Fin15AnchoredAtom4030 Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 9, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 9, 10, 13, 14}, {2, 9, 10, 12, 14}, {2, 9, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30152 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4152 chi ∧
      Fin15AnchoredAtom4362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4032 Fin15AnchoredAtom4033 Fin15AnchoredAtom4040
    Fin15AnchoredAtom4068 Fin15AnchoredAtom4152 Fin15AnchoredAtom4362 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 8}, {3, 5, 6, 7, 8}, {3, 4, 6, 7, 8}, {3, 4, 5, 7, 8}, {3, 4, 5, 6, 8}, {3, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30153 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4032 Fin15AnchoredAtom4034 Fin15AnchoredAtom4041
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4153 Fin15AnchoredAtom4363 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 9}, {3, 5, 6, 7, 9}, {3, 4, 6, 7, 9}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30154 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4032 Fin15AnchoredAtom4035 Fin15AnchoredAtom4042
    Fin15AnchoredAtom4070 Fin15AnchoredAtom4154 Fin15AnchoredAtom4364 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 10}, {3, 5, 6, 7, 10}, {3, 4, 6, 7, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30155 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4366 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4032 Fin15AnchoredAtom4037 Fin15AnchoredAtom4044
    Fin15AnchoredAtom4072 Fin15AnchoredAtom4156 Fin15AnchoredAtom4366 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 12}, {3, 5, 6, 7, 12}, {3, 4, 6, 7, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30156 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4367 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4032 Fin15AnchoredAtom4038 Fin15AnchoredAtom4045
    Fin15AnchoredAtom4073 Fin15AnchoredAtom4157 Fin15AnchoredAtom4367 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 13}, {3, 5, 6, 7, 13}, {3, 4, 6, 7, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30157 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4032 Fin15AnchoredAtom4039 Fin15AnchoredAtom4046
    Fin15AnchoredAtom4074 Fin15AnchoredAtom4158 Fin15AnchoredAtom4368 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 14}, {3, 5, 6, 7, 14}, {3, 4, 6, 7, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30158 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4047 chi ∧
      Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom4159 chi ∧
      Fin15AnchoredAtom4369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4033 Fin15AnchoredAtom4034 Fin15AnchoredAtom4047
    Fin15AnchoredAtom4075 Fin15AnchoredAtom4159 Fin15AnchoredAtom4369 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 9}, {3, 5, 6, 8, 9}, {3, 4, 6, 8, 9}, {3, 4, 5, 8, 9}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30159 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4160 chi ∧
      Fin15AnchoredAtom4370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4033 Fin15AnchoredAtom4035 Fin15AnchoredAtom4048
    Fin15AnchoredAtom4076 Fin15AnchoredAtom4160 Fin15AnchoredAtom4370 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 10}, {3, 5, 6, 8, 10}, {3, 4, 6, 8, 10}, {3, 4, 5, 8, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30160 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4050 chi ∧
      Fin15AnchoredAtom4078 chi ∧
      Fin15AnchoredAtom4162 chi ∧
      Fin15AnchoredAtom4372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4033 Fin15AnchoredAtom4037 Fin15AnchoredAtom4050
    Fin15AnchoredAtom4078 Fin15AnchoredAtom4162 Fin15AnchoredAtom4372 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 12}, {3, 5, 6, 8, 12}, {3, 4, 6, 8, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30161 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4034 Fin15AnchoredAtom4035 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4081 Fin15AnchoredAtom4165 Fin15AnchoredAtom4375 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 10}, {3, 5, 6, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30162 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4034 Fin15AnchoredAtom4037 Fin15AnchoredAtom4055
    Fin15AnchoredAtom4083 Fin15AnchoredAtom4167 Fin15AnchoredAtom4377 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 12}, {3, 5, 6, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30163 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4034 Fin15AnchoredAtom4038 Fin15AnchoredAtom4056
    Fin15AnchoredAtom4084 Fin15AnchoredAtom4168 Fin15AnchoredAtom4378 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 13}, {3, 5, 6, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30164 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4034 Fin15AnchoredAtom4039 Fin15AnchoredAtom4057
    Fin15AnchoredAtom4085 Fin15AnchoredAtom4169 Fin15AnchoredAtom4379 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 14}, {3, 5, 6, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30165 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4035 Fin15AnchoredAtom4037 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4087 Fin15AnchoredAtom4171 Fin15AnchoredAtom4381 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 12}, {3, 5, 6, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30166 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4035 Fin15AnchoredAtom4038 Fin15AnchoredAtom4060
    Fin15AnchoredAtom4088 Fin15AnchoredAtom4172 Fin15AnchoredAtom4382 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 13}, {3, 5, 6, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30167 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4035 Fin15AnchoredAtom4039 Fin15AnchoredAtom4061
    Fin15AnchoredAtom4089 Fin15AnchoredAtom4173 Fin15AnchoredAtom4383 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 14}, {3, 5, 6, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30168 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4037 Fin15AnchoredAtom4038 Fin15AnchoredAtom4065
    Fin15AnchoredAtom4093 Fin15AnchoredAtom4177 Fin15AnchoredAtom4387 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 13}, {3, 5, 6, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30169 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4388 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4037 Fin15AnchoredAtom4039 Fin15AnchoredAtom4066
    Fin15AnchoredAtom4094 Fin15AnchoredAtom4178 Fin15AnchoredAtom4388 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 14}, {3, 5, 6, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30170 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4038 Fin15AnchoredAtom4039 Fin15AnchoredAtom4067
    Fin15AnchoredAtom4095 Fin15AnchoredAtom4179 Fin15AnchoredAtom4389 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 13, 14}, {3, 5, 6, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30171 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4047 chi ∧
      Fin15AnchoredAtom4096 chi ∧
      Fin15AnchoredAtom4180 chi ∧
      Fin15AnchoredAtom4390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4040 Fin15AnchoredAtom4041 Fin15AnchoredAtom4047
    Fin15AnchoredAtom4096 Fin15AnchoredAtom4180 Fin15AnchoredAtom4390 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 9}, {3, 5, 7, 8, 9}, {3, 4, 7, 8, 9}, {3, 4, 5, 8, 9}, {3, 4, 5, 7, 9}, {3, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30172 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom4181 chi ∧
      Fin15AnchoredAtom4391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4040 Fin15AnchoredAtom4042 Fin15AnchoredAtom4048
    Fin15AnchoredAtom4097 Fin15AnchoredAtom4181 Fin15AnchoredAtom4391 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 10}, {3, 5, 7, 8, 10}, {3, 4, 7, 8, 10}, {3, 4, 5, 8, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30173 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4050 chi ∧
      Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom4183 chi ∧
      Fin15AnchoredAtom4393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4040 Fin15AnchoredAtom4044 Fin15AnchoredAtom4050
    Fin15AnchoredAtom4099 Fin15AnchoredAtom4183 Fin15AnchoredAtom4393 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 12}, {3, 5, 7, 8, 12}, {3, 4, 7, 8, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30174 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4051 chi ∧
      Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom4184 chi ∧
      Fin15AnchoredAtom4394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4040 Fin15AnchoredAtom4045 Fin15AnchoredAtom4051
    Fin15AnchoredAtom4100 Fin15AnchoredAtom4184 Fin15AnchoredAtom4394 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 13}, {3, 5, 7, 8, 13}, {3, 4, 7, 8, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30175 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4052 chi ∧
      Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom4185 chi ∧
      Fin15AnchoredAtom4395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4040 Fin15AnchoredAtom4046 Fin15AnchoredAtom4052
    Fin15AnchoredAtom4101 Fin15AnchoredAtom4185 Fin15AnchoredAtom4395 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 14}, {3, 5, 7, 8, 14}, {3, 4, 7, 8, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30176 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4041 Fin15AnchoredAtom4042 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4102 Fin15AnchoredAtom4186 Fin15AnchoredAtom4396 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 10}, {3, 5, 7, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30177 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4041 Fin15AnchoredAtom4044 Fin15AnchoredAtom4055
    Fin15AnchoredAtom4104 Fin15AnchoredAtom4188 Fin15AnchoredAtom4398 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 12}, {3, 5, 7, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30178 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4041 Fin15AnchoredAtom4045 Fin15AnchoredAtom4056
    Fin15AnchoredAtom4105 Fin15AnchoredAtom4189 Fin15AnchoredAtom4399 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 13}, {3, 5, 7, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30179 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4041 Fin15AnchoredAtom4046 Fin15AnchoredAtom4057
    Fin15AnchoredAtom4106 Fin15AnchoredAtom4190 Fin15AnchoredAtom4400 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 14}, {3, 5, 7, 9, 14}, {3, 4, 7, 9, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30180 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4042 Fin15AnchoredAtom4044 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4108 Fin15AnchoredAtom4192 Fin15AnchoredAtom4402 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 12}, {3, 5, 7, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30181 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4403 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4042 Fin15AnchoredAtom4045 Fin15AnchoredAtom4060
    Fin15AnchoredAtom4109 Fin15AnchoredAtom4193 Fin15AnchoredAtom4403 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 13}, {3, 5, 7, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30182 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4042 Fin15AnchoredAtom4046 Fin15AnchoredAtom4061
    Fin15AnchoredAtom4110 Fin15AnchoredAtom4194 Fin15AnchoredAtom4404 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 14}, {3, 5, 7, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30183 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4044 Fin15AnchoredAtom4045 Fin15AnchoredAtom4065
    Fin15AnchoredAtom4114 Fin15AnchoredAtom4198 Fin15AnchoredAtom4408 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 13}, {3, 5, 7, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30184 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4044 Fin15AnchoredAtom4046 Fin15AnchoredAtom4066
    Fin15AnchoredAtom4115 Fin15AnchoredAtom4199 Fin15AnchoredAtom4409 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 14}, {3, 5, 7, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30185 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4045 Fin15AnchoredAtom4046 Fin15AnchoredAtom4067
    Fin15AnchoredAtom4116 Fin15AnchoredAtom4200 Fin15AnchoredAtom4410 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 13, 14}, {3, 5, 7, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30186 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4047 chi ∧
      Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom4201 chi ∧
      Fin15AnchoredAtom4411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4047 Fin15AnchoredAtom4048 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4117 Fin15AnchoredAtom4201 Fin15AnchoredAtom4411 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 10}, {3, 5, 8, 9, 10}, {3, 4, 8, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 8, 10}, {3, 4, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30187 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4050 chi ∧
      Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4123 chi ∧
      Fin15AnchoredAtom4207 chi ∧
      Fin15AnchoredAtom4417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4048 Fin15AnchoredAtom4050 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4123 Fin15AnchoredAtom4207 Fin15AnchoredAtom4417 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 10, 12}, {3, 5, 8, 10, 12}, {3, 4, 8, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30188 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4051 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom4418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4048 Fin15AnchoredAtom4051 Fin15AnchoredAtom4060
    Fin15AnchoredAtom4124 Fin15AnchoredAtom4208 Fin15AnchoredAtom4418 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 10, 13}, {3, 5, 8, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30189 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4054 chi ∧
      Fin15AnchoredAtom4058 chi ∧
      Fin15AnchoredAtom4132 chi ∧
      Fin15AnchoredAtom4216 chi ∧
      Fin15AnchoredAtom4426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4053 Fin15AnchoredAtom4054 Fin15AnchoredAtom4058
    Fin15AnchoredAtom4132 Fin15AnchoredAtom4216 Fin15AnchoredAtom4426 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 9, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 11}, {3, 5, 9, 10, 11}, {3, 4, 9, 10, 11}, {3, 4, 5, 10, 11}, {3, 4, 5, 9, 11}, {3, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30190 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4053 Fin15AnchoredAtom4055 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4133 Fin15AnchoredAtom4217 Fin15AnchoredAtom4427 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30191 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4053 Fin15AnchoredAtom4056 Fin15AnchoredAtom4060
    Fin15AnchoredAtom4134 Fin15AnchoredAtom4218 Fin15AnchoredAtom4428 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30192 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4053 Fin15AnchoredAtom4057 Fin15AnchoredAtom4061
    Fin15AnchoredAtom4135 Fin15AnchoredAtom4219 Fin15AnchoredAtom4429 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30193 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4055 Fin15AnchoredAtom4056 Fin15AnchoredAtom4065
    Fin15AnchoredAtom4139 Fin15AnchoredAtom4223 Fin15AnchoredAtom4433 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30194 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4055 Fin15AnchoredAtom4057 Fin15AnchoredAtom4066
    Fin15AnchoredAtom4140 Fin15AnchoredAtom4224 Fin15AnchoredAtom4434 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30195 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4056 Fin15AnchoredAtom4057 Fin15AnchoredAtom4067
    Fin15AnchoredAtom4141 Fin15AnchoredAtom4225 Fin15AnchoredAtom4435 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30196 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4059 Fin15AnchoredAtom4060 Fin15AnchoredAtom4065
    Fin15AnchoredAtom4145 Fin15AnchoredAtom4229 Fin15AnchoredAtom4439 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30197 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4059 Fin15AnchoredAtom4061 Fin15AnchoredAtom4066
    Fin15AnchoredAtom4146 Fin15AnchoredAtom4230 Fin15AnchoredAtom4440 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30198 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4060 Fin15AnchoredAtom4061 Fin15AnchoredAtom4067
    Fin15AnchoredAtom4147 Fin15AnchoredAtom4231 Fin15AnchoredAtom4441 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30199 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4065 Fin15AnchoredAtom4066 Fin15AnchoredAtom4067
    Fin15AnchoredAtom4151 Fin15AnchoredAtom4235 Fin15AnchoredAtom4445 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30200 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom4096 chi ∧
      Fin15AnchoredAtom4236 chi ∧
      Fin15AnchoredAtom4446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4068 Fin15AnchoredAtom4069 Fin15AnchoredAtom4075
    Fin15AnchoredAtom4096 Fin15AnchoredAtom4236 Fin15AnchoredAtom4446 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 9}, {3, 6, 7, 8, 9}, {3, 4, 7, 8, 9}, {3, 4, 6, 8, 9}, {3, 4, 6, 7, 9}, {3, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30201 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom4237 chi ∧
      Fin15AnchoredAtom4447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4068 Fin15AnchoredAtom4070 Fin15AnchoredAtom4076
    Fin15AnchoredAtom4097 Fin15AnchoredAtom4237 Fin15AnchoredAtom4447 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 10}, {3, 6, 7, 8, 10}, {3, 4, 7, 8, 10}, {3, 4, 6, 8, 10}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30202 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4078 chi ∧
      Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom4239 chi ∧
      Fin15AnchoredAtom4449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4068 Fin15AnchoredAtom4072 Fin15AnchoredAtom4078
    Fin15AnchoredAtom4099 Fin15AnchoredAtom4239 Fin15AnchoredAtom4449 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 12}, {3, 6, 7, 8, 12}, {3, 4, 7, 8, 12}, {3, 4, 6, 8, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30203 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom4241 chi ∧
      Fin15AnchoredAtom4451 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4068 Fin15AnchoredAtom4074 Fin15AnchoredAtom4080
    Fin15AnchoredAtom4101 Fin15AnchoredAtom4241 Fin15AnchoredAtom4451 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 14}, {3, 6, 7, 8, 14}, {3, 4, 7, 8, 14}, {3, 4, 6, 8, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30204 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4069 Fin15AnchoredAtom4070 Fin15AnchoredAtom4081
    Fin15AnchoredAtom4102 Fin15AnchoredAtom4242 Fin15AnchoredAtom4452 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 10}, {3, 6, 7, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30205 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4069 Fin15AnchoredAtom4072 Fin15AnchoredAtom4083
    Fin15AnchoredAtom4104 Fin15AnchoredAtom4244 Fin15AnchoredAtom4454 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 12}, {3, 6, 7, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30206 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4069 Fin15AnchoredAtom4073 Fin15AnchoredAtom4084
    Fin15AnchoredAtom4105 Fin15AnchoredAtom4245 Fin15AnchoredAtom4455 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 13}, {3, 6, 7, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30207 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4069 Fin15AnchoredAtom4074 Fin15AnchoredAtom4085
    Fin15AnchoredAtom4106 Fin15AnchoredAtom4246 Fin15AnchoredAtom4456 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 14}, {3, 6, 7, 9, 14}, {3, 4, 7, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
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
