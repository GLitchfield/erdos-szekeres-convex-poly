module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment121

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 122. -/

theorem synchronizedFiveFanFin11Semantic_clause08756 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1174 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1178 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1194 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1246 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1309 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1174 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1178 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1194 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1246 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1309 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 7, 8}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0470
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08757 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1174 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1179 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1195 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1247 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1310 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1174 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1179 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1195 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1247 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1310 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 7, 9}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0726
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08758 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1174 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1179 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1195 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1247 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1310 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1174 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1179 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1195 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1247 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1310 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 7, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0726
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08759 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1614 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1757 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1614 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1617 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1620 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1636 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1757 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 7, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1238
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08760 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1174 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1180 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1196 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1248 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1311 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1174 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1180 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1196 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1248 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1311 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 7, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1238
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08761 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1174 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1180 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1196 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1248 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1311 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1174 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1180 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1196 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1248 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1311 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 7, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1238
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08762 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1614 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1757 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1614 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1617 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1620 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1636 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1757 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 7, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1238
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08763 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1249 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1312 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1312 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0854
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08764 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1249 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1312 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1312 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0854
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08765 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1249 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1312 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1312 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0854
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08766 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1249 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1312 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1312 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0854
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08767 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1182 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1198 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1250 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1313 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1198 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1250 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1313 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 8, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1366
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08768 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1182 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1198 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1250 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1313 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1198 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1250 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1313 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 8, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1366
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08769 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1175 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1182 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1198 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1250 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1313 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1175 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1198 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1250 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1313 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 8, 10}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1366
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08770 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1615 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1622 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1691 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1759 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1615 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1617 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1622 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1691 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1759 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1366
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08771 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1314 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1622
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08772 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1616 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1760 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1616 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1617 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1623 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1760 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1622
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08773 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1314 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1622
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08774 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1314 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1622
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08775 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1314 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 9, 10}, 7, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1622
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08776 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1176 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1314 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1176 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1622
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08777 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1616 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1760 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1616 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1617 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1623 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1760 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 6, 9, 10}, 8, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1622
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08778 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1618 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1622 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1640 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1761 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1618 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1620 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1622 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1640 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1693 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1761 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 7, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1430
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08779 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1619 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1762 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1619 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1620 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1623 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1641 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1694 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1762 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 7, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1686
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08780 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1619 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1762 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1619 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1620 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1623 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1641 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1694 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1762 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 7, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1686
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08781 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1179 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1180 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1200 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1253 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1317 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1179 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1180 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1200 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1253 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1317 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 7, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1686
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08782 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1182 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1318 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1318 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 8, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1814
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

theorem synchronizedFiveFanFin11Semantic_clause08783 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1182 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1318 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1318 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 8, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1814
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

theorem synchronizedFiveFanFin11Semantic_clause08784 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1621 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1622 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1763 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1621 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1622 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1623 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1695 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1763 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 8, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1814
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08785 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1182 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1318 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1318 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 8, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1814
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

theorem synchronizedFiveFanFin11Semantic_clause08786 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1182 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1318 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1318 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 8, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1814
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

theorem synchronizedFiveFanFin11Semantic_clause08787 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1628 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1634 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1764 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1624 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1625 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1628 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1634 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1696 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1764 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 7, 8}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0486
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08788 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1629 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1697 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1765 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1624 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1629 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1635 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1697 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1765 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 7, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0742
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08789 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1184 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1186 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1189 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1195 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1256 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1320 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1184 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1189 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1195 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1256 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1320 at h20
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0742
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

theorem synchronizedFiveFanFin11Semantic_clause08790 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1184 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1186 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1189 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1195 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1256 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1320 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1184 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1189 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1195 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1256 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1320 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 7, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0742
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

theorem synchronizedFiveFanFin11Semantic_clause08791 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1766 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1624 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1627 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1630 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1636 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1698 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1766 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 7, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1254
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08792 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1184 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1187 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1190 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1196 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1257 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1321 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1184 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1187 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1190 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1196 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1257 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1321 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 7, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1254
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08793 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1185 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1186 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1191 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1258 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1322 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1185 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1191 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1258 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1322 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0870
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08794 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1767 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1625 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1631 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0870
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08795 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1767 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1625 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1631 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0870
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08796 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1767 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1625 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1631 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0870
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08797 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1185 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1186 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1191 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1258 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1322 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1185 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1191 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1258 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1322 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0870
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08798 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1768 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1625 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1627 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1768 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 8, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1382
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

theorem synchronizedFiveFanFin11Semantic_clause08799 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1768 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1625 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1627 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1768 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 8, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1382
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

theorem synchronizedFiveFanFin11Semantic_clause08800 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1768 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1625 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1627 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1768 at h20
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1382
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

theorem synchronizedFiveFanFin11Semantic_clause08801 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1186 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1187 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1193 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1187 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1638
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08802 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1769 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1627 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1769 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1638
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

theorem synchronizedFiveFanFin11Semantic_clause08803 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1186 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1187 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1193 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1187 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1638
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08804 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1769 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1627 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1769 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1638
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

theorem synchronizedFiveFanFin11Semantic_clause08805 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1769 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1627 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1769 at h20
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1638
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

theorem synchronizedFiveFanFin11Semantic_clause08806 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1769 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1627 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1769 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 9, 10}, 7, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1638
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

theorem synchronizedFiveFanFin11Semantic_clause08807 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1186 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1187 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1193 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1187 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1638
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08808 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1629 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1772 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1629 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1630 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1641 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1704 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1772 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 7, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1702
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08809 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1189 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1190 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1193 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1200 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1263 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1327 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1189 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1190 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1200 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1263 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1327 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 7, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1702
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08810 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1629 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1772 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1629 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1630 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1641 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1704 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1772 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 7, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1702
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08811 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1189 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1190 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1193 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1200 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1263 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1327 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1189 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1190 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1200 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1263 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1327 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1702
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08812 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1773 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1631 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1773 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 8, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1830
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08813 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1773 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1631 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1773 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 8, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1830
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08814 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1191 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1192 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1193 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1264 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1191 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1192 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1264 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 8, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1830
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08815 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1773 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1631 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1773 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 8, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1830
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08816 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1775 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1635 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1636 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1641 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1708 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1775 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 7, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1734
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08817 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1775 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1635 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1636 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1641 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1708 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1775 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 7, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1734
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08818 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1775 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1635 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1636 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1641 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1708 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1775 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 7, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1734
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08819 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1195 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1196 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1200 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1265 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1331 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1195 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1196 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1200 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1265 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1331 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1734
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08820 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1198 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1266 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1332 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1198 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1266 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 8, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1862
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08821 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1198 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1266 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1332 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1198 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1266 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 8, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1862
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08822 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1776 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1709 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1776 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 8, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1862
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08823 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1776 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1709 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1776 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 8, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1862
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08824 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1198 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1266 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1332 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1198 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1266 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 8, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1862
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08825 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1776 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1709 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1776 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 6, 8, 9, 10}, 7, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1862
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08826 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1643 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1644 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1648 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1657 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1777 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1643 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1644 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1648 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1657 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1677 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1777 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 4, 5, 6, 7}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0250
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
