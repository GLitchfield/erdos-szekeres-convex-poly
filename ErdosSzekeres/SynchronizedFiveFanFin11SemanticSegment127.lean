module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment126

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 127. -/

theorem synchronizedFiveFanFin11Semantic_clause09111 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1320 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1321 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1327 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1331 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1381 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1320 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1321 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1327 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1331 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1381 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 5, 6, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1764
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

theorem synchronizedFiveFanFin11Semantic_clause09112 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1322 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1323 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1332 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1322 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1323 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 5, 6, 8, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1892
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09113 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1322 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1323 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1332 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1322 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1323 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 5, 6, 8, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1892
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09114 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1322 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1323 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1332 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1322 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1323 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1332 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 5, 6, 8, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1892
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09115 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1768 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1769 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1773 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1776 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1821 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1768 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1769 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1773 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1776 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1821 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 5, 6, 8, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1892
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09116 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1768 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1769 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1773 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1776 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1821 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1768 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1769 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1773 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1776 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1821 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 5, 6, 8, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1892
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09117 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1325 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1326 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1327 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1333 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1383 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1325 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1326 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1327 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1333 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1383 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 5, 7, 8, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1956
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 5, 7, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 7, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 7, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 7, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 7, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09118 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1777 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1779 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1781 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1786 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1794 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1807 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1777 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1779 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1781 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1786 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1794 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1807 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 7, 9}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0760
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09119 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1334 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1340 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1346 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1354 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1368 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1334 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1340 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1346 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1354 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1368 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 7, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1272
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09120 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1334 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1340 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1346 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1354 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1368 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1334 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1340 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1346 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1354 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1368 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 7, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1272
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09121 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1777 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1782 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1795 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1808 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1777 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1780 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1782 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1787 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1795 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1808 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 7, 10}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1272
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09122 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1777 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1782 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1795 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1808 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1777 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1780 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1782 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1787 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1795 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1808 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 7, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1272
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09123 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1335 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1347 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1355 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1369 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1335 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1341 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1347 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1355 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1369 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0888
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09124 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1335 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1347 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1355 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1369 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1335 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1341 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1347 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1355 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1369 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 8, 9}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0888
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09125 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1335 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1347 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1355 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1369 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1335 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1341 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1347 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1355 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1369 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 8, 9}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0888
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09126 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1778 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1779 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1788 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1809 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1778 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1779 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1783 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1788 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1809 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0888
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09127 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1335 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1356 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1370 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1335 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1342 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1356 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 8, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1400
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09128 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1335 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1356 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1370 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1335 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1342 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1356 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 8, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1400
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09129 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1335 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1356 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1370 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1335 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1342 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1356 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 8, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1400
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09130 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1778 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1784 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1789 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1810 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1778 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1780 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1784 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1789 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1797 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1810 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1400
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09131 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1357 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1656
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

theorem synchronizedFiveFanFin11Semantic_clause09132 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1357 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1656
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

theorem synchronizedFiveFanFin11Semantic_clause09133 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1357 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1656
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

theorem synchronizedFiveFanFin11Semantic_clause09134 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1779 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1785 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1798 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1811 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1779 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1780 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1785 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1790 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1798 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1811 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1656
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09135 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1336 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1357 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1336 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1337 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h20
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1656
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

theorem synchronizedFiveFanFin11Semantic_clause09136 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1779 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1785 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1798 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1811 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1779 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1780 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1785 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1790 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1798 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1811 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 6, 9, 10}, 8, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1656
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09137 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1338 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1339 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1350 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1358 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1372 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1338 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1339 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1341 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1350 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1358 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1372 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 7, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0952
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09138 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1338 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1340 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1351 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1359 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1373 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1338 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1340 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1342 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1351 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1359 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1373 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 7, 8, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1464
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09139 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1339 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1340 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1352 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1360 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1374 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1339 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1340 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1352 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1360 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 7, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1720
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09140 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1339 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1340 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1352 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1360 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1374 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1339 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1340 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1352 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1360 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1720
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09141 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1341 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1342 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 8, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1848
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09142 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1341 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1342 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 8, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1848
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09143 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1341 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1342 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 8, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1848
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09144 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1784 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1785 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1792 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1814 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1783 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1784 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1785 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1792 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1802 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1814 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1848
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09145 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1341 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1342 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 5, 8, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1848
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09146 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1344 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1346 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1351 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1362 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1377 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1344 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1346 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1351 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1362 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1377 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 7, 8, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1496
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09147 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1786 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1791 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1804 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1816 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1786 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1787 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1790 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1791 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1804 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1816 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 7, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1752
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09148 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1786 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1791 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1804 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1816 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1786 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1787 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1790 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1791 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1804 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1816 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 7, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1752
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09149 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1345 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1346 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1352 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1363 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1378 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1345 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1346 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1352 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1363 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1378 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 7, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1752
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09150 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1345 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1346 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1352 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1363 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1378 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1345 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1346 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1352 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1363 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1378 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1752
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09151 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1347 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1364 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1347 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 8, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1880
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09152 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1788 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1789 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1792 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1817 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1788 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1789 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1790 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1792 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1817 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 8, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1880
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09153 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1347 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1364 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1347 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 8, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1880
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09154 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1347 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1364 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1347 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 8, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1880
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09155 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1788 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1789 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1792 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1817 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1788 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1789 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1790 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1792 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1817 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1880
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09156 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1347 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1364 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1347 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 8, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1880
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09157 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1350 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1351 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1352 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1365 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1380 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1350 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1351 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1352 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1365 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1380 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 7, 8, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1944
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 7, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 7, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 7, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09158 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1793 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1794 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1799 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1818 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1793 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1794 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1799 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1803 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1818 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 5, 6, 7, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1000
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 5, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {5, 6, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09159 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1355 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1356 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1357 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1364 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1355 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1356 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 5, 6, 8, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1896
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09160 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1798 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1821 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1797 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1798 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1802 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1821 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 5, 6, 8, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1896
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09161 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1355 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1356 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1357 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1364 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1355 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1356 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 5, 6, 8, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1896
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09162 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1355 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1356 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1357 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1364 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1355 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1356 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 5, 6, 8, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1896
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09163 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1798 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1821 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1797 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1798 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1802 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1821 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 5, 6, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1896
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09164 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1798 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1821 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1797 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1798 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1802 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1821 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 5, 6, 8, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1896
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09165 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1367 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1368 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1374 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1378 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1381 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1367 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1368 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1378 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1381 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 6, 7, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1776
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09166 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1367 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1368 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1374 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1378 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1381 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1367 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1368 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1378 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1381 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 6, 7, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1776
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09167 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1367 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1368 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1374 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1378 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1381 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1367 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1368 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1378 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1381 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 6, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1776
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09168 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1807 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1808 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1811 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1813 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1816 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1820 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1807 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1808 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1811 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1813 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1816 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1820 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 6, 7, 9, 10}, 8, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1776
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {5, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09169 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1369 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1370 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1369 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 6, 8, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1904
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09170 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1369 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1370 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1369 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 6, 8, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1904
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09171 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1369 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1370 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1369 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 6, 8, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1904
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09172 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1809 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1810 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1811 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1814 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1817 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1821 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1809 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1810 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1811 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1814 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1817 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1821 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 6, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1904
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09173 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1369 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1370 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1369 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 6, 8, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1904
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09174 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1372 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1373 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1374 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1380 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1383 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1372 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1373 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1380 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1383 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 5, 7, 8, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1968
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {4, 5, 7, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 7, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {5, 7, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09175 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1376 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1377 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1378 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1380 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1384 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1376 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1377 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1378 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1380 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1384 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{4, 6, 7, 8, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask2000
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {4, 6, 7, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 7, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {6, 7, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause09176 (chi : TripleColoring 11)
    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0015 chi) := by
  unfold SynchronizedFiveFanFin11SelectedCube at hcube
  unfold SynchronizedFiveFanFin11SemanticAtom0015
  rcases hcube with ⟨h0, h1, h2, h3, h4, h5⟩
  simp_all

theorem synchronizedFiveFanFin11Semantic_clause09177 (chi : TripleColoring 11)
    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0111 chi) := by
  unfold SynchronizedFiveFanFin11SelectedCube at hcube
  unfold SynchronizedFiveFanFin11SemanticAtom0111
  rcases hcube with ⟨h0, h1, h2, h3, h4, h5⟩
  simp_all

theorem synchronizedFiveFanFin11Semantic_clause09178 (chi : TripleColoring 11)
    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  unfold SynchronizedFiveFanFin11SelectedCube at hcube
  unfold SynchronizedFiveFanFin11SemanticAtom0155
  rcases hcube with ⟨h0, h1, h2, h3, h4, h5⟩
  simp_all

theorem synchronizedFiveFanFin11Semantic_clause09179 (chi : TripleColoring 11)
    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0068 chi) := by
  unfold SynchronizedFiveFanFin11SelectedCube at hcube
  unfold SynchronizedFiveFanFin11SemanticAtom0068
  rcases hcube with ⟨h0, h1, h2, h3, h4, h5⟩
  simp_all

theorem synchronizedFiveFanFin11Semantic_clause09180 (chi : TripleColoring 11)
    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0142 chi) := by
  unfold SynchronizedFiveFanFin11SelectedCube at hcube
  unfold SynchronizedFiveFanFin11SemanticAtom0142
  rcases hcube with ⟨h0, h1, h2, h3, h4, h5⟩
  simp_all

theorem synchronizedFiveFanFin11Semantic_clause09181 (chi : TripleColoring 11)
    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0002 chi) := by
  unfold SynchronizedFiveFanFin11SelectedCube at hcube
  unfold SynchronizedFiveFanFin11SemanticAtom0002
  rcases hcube with ⟨h0, h1, h2, h3, h4, h5⟩
  simp_all

end ErdosSzekeres

end
